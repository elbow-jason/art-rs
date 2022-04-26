use crate::node::*;
use crate::{Key, Leaf, TypedNode};
use std::collections::{BinaryHeap, VecDeque};
use std::ops::{Bound, RangeBounds};

pub struct Scanner<'a, K, V, R> {
    forward: ScannerState<'a, K, V>,
    last_forward_key: Option<&'a K>,
    backward: BackwardScannerState<'a, K, V>,
    last_backward_key: Option<&'a K>,
    range: R,
}

struct ScannerState<'a, K, V> {
    interims: Vec<NodeIter<'a, TypedNode<K, V>>>,
    leafs: VecDeque<&'a Leaf<K, V>>,
}

struct BackwardScannerState<'a, K, V> {
    interims: Vec<NodeIter<'a, TypedNode<K, V>>>,
    leafs: BinaryHeap<&'a Leaf<K, V>>,
}

impl<'a, K, V, R> Scanner<'a, K, V, R>
where
    K: Key + Ord,
    R: RangeBounds<K>,
{
    pub(crate) fn empty(range: R) -> Self {
        Self {
            forward: ScannerState::empty(),
            backward: BackwardScannerState::empty(),
            last_forward_key: None,
            last_backward_key: None,
            range,
        }
    }

    pub(crate) fn new(node: &'a TypedNode<K, V>, range: R) -> Self
    where
        R: RangeBounds<K>,
    {
        Self {
            forward: ScannerState::forward_scan(node, &range),
            backward: BackwardScannerState::backward_scan(node, &range),
            last_forward_key: None,
            last_backward_key: None,
            range,
        }
    }
}

impl<'a, K, V> ScannerState<'a, K, V>
where
    K: Ord,
{
    pub(crate) fn empty() -> Self {
        Self {
            interims: Vec::new(),
            leafs: VecDeque::new(),
        }
    }

    fn forward_scan<R>(node: &'a TypedNode<K, V>, range: &R) -> Self
    where
        R: RangeBounds<K>,
    {
        let mut node = node;
        let mut leafs = VecDeque::new();
        let mut interims = Vec::new();
        loop {
            match node {
                TypedNode::Leaf(leaf) => {
                    if range.contains(&leaf.key) {
                        leafs.push_back(leaf);
                    }
                    break;
                }
                TypedNode::Interim(interim) => {
                    interims.push(interim.iter());
                    break;
                }
                TypedNode::Combined(interim, leaf) => {
                    node = interim;
                    if range.contains(&leaf.key) {
                        leafs.push_back(leaf);
                    }
                }
            }
        }

        Self { interims, leafs }
    }
}

impl<'a, K, V> BackwardScannerState<'a, K, V>
where
    K: Ord,
{
    pub(crate) fn empty() -> Self {
        Self {
            interims: Vec::new(),
            leafs: BinaryHeap::new(),
        }
    }

    fn backward_scan<R>(node: &'a TypedNode<K, V>, range: &R) -> Self
    where
        R: RangeBounds<K>,
    {
        let mut node = node;
        let mut leafs = BinaryHeap::new();
        let mut interims = Vec::new();
        loop {
            match node {
                TypedNode::Leaf(leaf) => {
                    if range.contains(&leaf.key) {
                        leafs.push(leaf);
                    }
                    break;
                }
                TypedNode::Interim(interim) => {
                    interims.push(interim.iter());
                    break;
                }
                TypedNode::Combined(interim, leaf) => {
                    node = interim;
                    if range.contains(&leaf.key) {
                        leafs.push(leaf);
                    }
                }
            }
        }

        Self { interims, leafs }
    }
}

impl<'a, K: Key + Ord, V, R: RangeBounds<K>> DoubleEndedIterator for Scanner<'a, K, V, R> {
    fn next_back(&mut self) -> Option<Self::Item> {
        'outer: while let Some(node) = self.backward.interims.last_mut() {
            let mut e = node.next_back();
            loop {
                match e {
                    Some(TypedNode::Leaf(leaf)) => {
                        if self.range.contains(&leaf.key) {
                            self.backward.leafs.push(leaf);
                            break 'outer;
                        } else {
                            match self.range.start_bound() {
                                Bound::Included(k) if &leaf.key < k => {
                                    self.backward.interims.clear()
                                }
                                Bound::Excluded(k) if &leaf.key <= k => {
                                    self.backward.interims.clear()
                                }
                                _ => {}
                            }
                        }
                        break;
                    }
                    Some(TypedNode::Interim(interim)) => {
                        self.backward.interims.push(interim.iter());
                        break;
                    }
                    Some(TypedNode::Combined(interim, leaf)) => {
                        if self.range.contains(&leaf.key) {
                            self.backward.leafs.push(leaf);
                        }
                        // next interim can be combined node
                        e = Some(interim);
                    }
                    None => {
                        self.backward.interims.pop().unwrap();
                        break;
                    }
                }
            }
        }

        self.backward.leafs.pop().and_then(|leaf| {
            self.last_backward_key = Some(&leaf.key);
            if self
                .last_backward_key
                .zip(self.last_forward_key)
                .map_or(true, |(k1, k2)| k1 > k2)
            {
                Some((&leaf.key, &leaf.value))
            } else {
                self.backward.interims.clear();
                self.backward.leafs.clear();
                None
            }
        })
    }
}

impl<'a, K: 'a + Key + Ord, V, R: RangeBounds<K>> Iterator for Scanner<'a, K, V, R> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        'outer: while let Some(node) = self.forward.interims.last_mut() {
            let mut e = node.next();
            loop {
                match e {
                    Some(TypedNode::Leaf(leaf)) => {
                        if self.range.contains(&leaf.key) {
                            self.forward.leafs.push_back(leaf);
                            break 'outer;
                        } else {
                            match self.range.end_bound() {
                                Bound::Included(k) if &leaf.key > k => {
                                    self.forward.interims.clear()
                                }
                                Bound::Excluded(k) if &leaf.key >= k => {
                                    self.forward.interims.clear()
                                }
                                _ => {}
                            }
                        }

                        break;
                    }
                    Some(TypedNode::Interim(interim)) => {
                        self.forward.interims.push(interim.iter());
                        break;
                    }
                    Some(TypedNode::Combined(interim, leaf)) => {
                        if self.range.contains(&leaf.key) {
                            self.forward.leafs.push_back(leaf);
                            // next interim can be combined node
                            e = Some(interim);
                        } else {
                            match self.range.end_bound() {
                                Bound::Included(k) if &leaf.key > k => {
                                    self.forward.interims.clear()
                                }
                                Bound::Excluded(k) if &leaf.key >= k => {
                                    self.forward.interims.clear()
                                }
                                _ => {}
                            }
                            break;
                        }
                    }
                    None => {
                        self.forward.interims.pop().unwrap();
                        break;
                    }
                }
            }
        }

        self.forward.leafs.pop_front().and_then(|leaf| {
            self.last_forward_key = Some(&leaf.key);
            if self
                .last_forward_key
                .zip(self.last_backward_key)
                .map_or(true, |(k1, k2)| k1 < k2)
            {
                Some((&leaf.key, &leaf.value))
            } else {
                self.forward.interims.clear();
                self.forward.leafs.clear();
                None
            }
        })
    }
}

#[cfg(test)]
mod tests {
    use crate::{Art, Float32, Float64, Key};
    use rand::prelude::SliceRandom;
    use rand::{thread_rng, Rng};
    use std::cmp;
    use std::collections::HashSet;

    fn compound_key<A: Key, B: Key>(a: A, b: B) -> Vec<u8> {
        let mut key = vec_key(a);
        key.extend(b.to_bytes().as_slice());
        key
    }

    fn vec_key<K: Key>(k: K) -> Vec<u8> {
        k.to_bytes().as_slice().to_vec()
    }

    #[test]
    fn combined_keys() {
        let mut art = Art::new();
        for i in 0..=u8::MAX {
            for j in i8::MIN..=i8::MAX {
                let key = compound_key(i, j);
                assert!(art.insert(key, i.to_string()), "{}", i);
            }
        }

        let mut it = art.iter();
        for i in 0..=u8::MAX {
            for j in i8::MIN..=i8::MAX {
                let key = compound_key(i, j);
                assert!(matches!(it.next(), Some((k, val)) if &key == k && val == &i.to_string()));
            }
        }

        assert!(it.next().is_none());
    }

    #[test]
    fn seq_u8() {
        let mut art = Art::new();
        for i in 0..=u8::MAX {
            assert!(art.insert(i, i.to_string()), "{}", i);
        }

        let mut len = 0usize;
        let mut expected = 0u8;
        for (k, v) in art.range(0u8..=u8::MAX) {
            assert_eq!(&expected, k);
            assert_eq!(&expected.to_string(), v);
            expected = expected.wrapping_add(1);
            len += 1;
        }
        assert_eq!(len, u8::MAX as usize + 1);
    }

    #[test]
    fn seq_u16() {
        let mut art = Art::new();
        for i in 0..=u16::MAX {
            assert!(art.insert(i, i.to_string()), "{}", i);
        }

        let mut len = 0usize;
        let mut expected = 0u16;
        for (k, v) in art.range(0u16..=u16::MAX) {
            assert_eq!(&expected, k);
            assert_eq!(&expected.to_string(), v);
            expected = expected.wrapping_add(1);
            len += 1;
        }
        assert_eq!(len, u16::MAX as usize + 1);
    }

    #[test]
    fn range_scan_on_sequential_u32_keys() {
        let mut art = Art::new();
        for shift in 0..2 {
            let start = (u16::MAX as u32 + 1) << (shift * 8);
            let end = start + 10000;
            for i in start..=end {
                assert!(art.insert(i, i.to_string()), "{}", i);
            }

            let mut len = 0;
            let mut expected = start;
            for (k, v) in art.range(start..=end) {
                assert_eq!(&expected, k);
                assert_eq!(&expected.to_string(), v);
                expected += 1;
                len += 1;
            }
            assert_eq!(len, end - start + 1);
        }
    }

    #[test]
    fn range_scan_on_sequential_f32_keys() {
        let mut all_keys = Vec::new();
        let mut art: Art<Float32, String> = Art::new();
        let mut next = thread_rng().gen_range(0.0..1000.0);
        let end = next + 50.0;
        while next < end {
            art.insert(next.into(), next.to_string());
            all_keys.push(next);
            let step = thread_rng().gen_range(1.1..2.5);
            next += step;
        }

        for _ in 0..100 {
            let start_idx = thread_rng().gen_range(0..all_keys.len());
            let end_idx = thread_rng().gen_range(start_idx..all_keys.len());
            let range = Float32::from(all_keys[start_idx])..=Float32::from(all_keys[end_idx]);
            assert_eq!(art.range(range).count(), end_idx - start_idx + 1);
        }

        assert_eq!(art.iter().count(), all_keys.len());

        let mut art: Art<Float32, String> = Art::new();
        art.insert(f32::NEG_INFINITY.into(), f32::NEG_INFINITY.to_string());
        art.insert(f32::MIN.into(), f32::MIN.to_string());
        art.insert(f32::MIN_POSITIVE.into(), f32::MIN_POSITIVE.to_string());
        art.insert(f32::MAX.into(), f32::MAX.to_string());
        art.insert(f32::INFINITY.into(), f32::INFINITY.to_string());
        art.insert(f32::NAN.into(), f32::NAN.to_string());
        let mut iter = art.iter();
        assert!(matches!(iter.next(), Some((_, val)) if val == &f32::MIN.to_string()));
        assert!(matches!(iter.next(), Some((_, val)) if val == &f32::NEG_INFINITY.to_string()));
        assert!(matches!(iter.next(), Some((_, val)) if val == &f32::MIN_POSITIVE.to_string()));
        assert!(matches!(iter.next(), Some((_, val)) if val == &f32::MAX.to_string()));
        assert!(matches!(iter.next(), Some((_, val)) if val == &f32::INFINITY.to_string()));
        assert!(matches!(iter.next(), Some((_, val)) if val == &f32::NAN.to_string()));
    }

    #[test]
    fn range_scan_on_sequential_u64_keys() {
        let mut art = Art::new();
        for shift in 0..4 {
            let start = (u32::MAX as u64 + 1) << (shift * 8);
            let end = start + 100_000;
            for i in start..=end {
                art.insert(i, i.to_string());
            }

            let mut len = 0;
            let mut expected = start;
            for (k, v) in art.range(start..=end) {
                assert_eq!(&expected, k);
                assert_eq!(&expected.to_string(), v);
                expected += 1;
                len += 1;
            }
            assert_eq!(len, end - start + 1);
        }
    }

    #[test]
    fn range_scan_on_sequential_f64_keys() {
        let mut all_keys = Vec::new();
        let mut art: Art<Float64, String> = Art::new();
        let mut next = thread_rng().gen_range(0.0..1000.0);
        let end = next + 50.0;
        while next < end {
            art.insert(next.into(), next.to_string());
            all_keys.push(next);
            let step = thread_rng().gen_range(1.1..2.5);
            next += step;
        }

        for _ in 0..100 {
            let start_idx = thread_rng().gen_range(0..all_keys.len());
            let end_idx = thread_rng().gen_range(start_idx..all_keys.len());
            let range = Float64::from(all_keys[start_idx])..=Float64::from(all_keys[end_idx]);
            assert_eq!(art.range(range).count(), end_idx - start_idx + 1);
        }

        assert_eq!(art.iter().count(), all_keys.len());

        let mut art: Art<Float64, String> = Art::new();
        art.insert(f64::NEG_INFINITY.into(), f64::NEG_INFINITY.to_string());
        art.insert(f64::MIN.into(), f64::MIN.to_string());
        art.insert(f64::MIN_POSITIVE.into(), f64::MIN_POSITIVE.to_string());
        art.insert(f64::MAX.into(), f64::MAX.to_string());
        art.insert(f64::INFINITY.into(), f64::INFINITY.to_string());
        art.insert(f64::NAN.into(), f64::NAN.to_string());
        let mut iter = art.iter();
        assert!(matches!(iter.next(), Some((_, val)) if val == &f64::MIN.to_string()));
        assert!(matches!(iter.next(), Some((_, val)) if val == &f64::NEG_INFINITY.to_string()));
        assert!(matches!(iter.next(), Some((_, val)) if val == &f64::MIN_POSITIVE.to_string()));
        assert!(matches!(iter.next(), Some((_, val)) if val == &f64::MAX.to_string()));
        assert!(matches!(iter.next(), Some((_, val)) if val == &f64::INFINITY.to_string()));
        assert!(matches!(iter.next(), Some((_, val)) if val == &f64::NAN.to_string()));
    }

    #[test]
    fn iter_with_long_prefix() {
        let mut art: Art<Vec<u8>, Vec<u8>> = Art::new();
        let mut existing: HashSet<Vec<u8>> = HashSet::new();
        long_prefix_test(&mut art, |art, key| {
            let vk = vec_key(key.clone());
            assert!(
                art.insert(vk.clone(), key.clone()),
                "{:?} already exists",
                key
            );
            existing.insert(vk);
        });

        let mut sorted: Vec<Vec<u8>> = existing.iter().cloned().collect();
        sorted.sort();
        assert_eq!(
            sorted,
            art.iter().map(|(_, v)| v.clone()).collect::<Vec<Vec<u8>>>()
        );

        sorted
            .choose_multiple(&mut thread_rng(), sorted.len() / 4)
            .for_each(|key| {
                art.remove(&key);
                existing.remove(key);
            });

        let mut sorted: Vec<Vec<u8>> = existing.iter().cloned().collect();
        sorted.sort();
        assert_eq!(
            sorted,
            art.iter().map(|(_, v)| v.clone()).collect::<Vec<Vec<u8>>>()
        );
    }

    #[test]
    fn range_scan_with_long_prefix() {
        let mut art = Art::new();
        long_prefix_test(&mut art, |art, key| {
            let vk = vec_key(key.clone());
            art.insert(vk, key);
        });

        let keys: Vec<Vec<u8>> = art.iter().map(|(k, _)| k.clone()).collect();
        for _ in 0..500 {
            let bound1 = keys.choose(&mut thread_rng()).unwrap();
            let bound2 = keys.choose(&mut thread_rng()).unwrap();
            let range = cmp::min(bound1, bound2)..cmp::max(bound1, bound2);
            art.range(range.clone())
                .map(|(k, _)| k.clone())
                .all(|k| range.contains(&&k));
            let range = cmp::min(bound1, bound2)..=cmp::max(bound1, bound2);
            art.range(range.clone())
                .map(|(k, _)| k.clone())
                .all(|k| range.contains(&&k));
            let range = ..cmp::max(bound1, bound2);
            art.range(range)
                .map(|(k, _)| k.clone())
                .all(|k| range.contains(&&k));
            let range = ..=cmp::max(bound1, bound2);
            art.range(range)
                .map(|(k, _)| k.clone())
                .all(|k| range.contains(&&k));
            let range = cmp::max(bound1, bound2)..;
            art.range(range.clone())
                .map(|(k, _)| k.clone())
                .all(|k| range.contains(&&k));
        }
        // TODO: add test for range scans which starts with non-existing keys
    }

    #[test]
    fn double_ended_iter() {
        let mut art = Art::new();
        let mut existing = HashSet::new();
        long_prefix_test(&mut art, |art, k| {
            let key = vec_key(k.clone());
            art.insert(key, k.clone());
            existing.insert(k);
        });

        let mut iter = art.iter().peekable();
        let mut fwd = Vec::new();
        let mut bwd = Vec::new();
        while iter.peek().is_some() {
            if thread_rng().gen_bool(0.5) {
                let hi: usize = thread_rng().gen_range(1..25);
                (0..hi).for_each(|_| {
                    iter.next().map(|(_, v)| fwd.push(v.clone()));
                });
            } else {
                let hi: usize = thread_rng().gen_range(1..25);
                (0..hi).for_each(|_| {
                    iter.next_back().map(|(_, v)| bwd.push(v.clone()));
                });
            }
        }

        let mut expected: Vec<Vec<u8>> = existing.iter().cloned().collect();
        expected.sort();
        bwd.reverse();
        fwd.append(&mut bwd);
        assert_eq!(expected, fwd);
    }

    #[test]
    fn double_ended_iter_seq_keys() {
        let mut art = Art::new();
        for i in 0..2500u32 {
            art.insert(i, i);

            let mut iter = art.iter().peekable();
            let mut fwd = Vec::new();
            let mut bwd = Vec::new();
            while iter.peek().is_some() {
                if thread_rng().gen_bool(0.5) {
                    (0..thread_rng().gen_range(1..25)).for_each(|_| {
                        iter.next().map(|(_, v)| fwd.push(v.clone()));
                    });
                } else {
                    (0..thread_rng().gen_range(1..25)).for_each(|_| {
                        iter.next_back().map(|(_, v)| bwd.push(v.clone()));
                    });
                }
            }

            let expected: Vec<u32> = (0..=i).collect();
            bwd.reverse();
            fwd.append(&mut bwd);
            assert_eq!(expected, fwd);
        }
    }

    fn long_prefix_test<F: FnMut(&mut Art<Vec<u8>, Vec<u8>>, Vec<u8>)>(
        art: &mut Art<Vec<u8>, Vec<u8>>,
        mut test_fn: F,
    ) {
        let mut existing = HashSet::new();
        let mut chars: Vec<u8> = (0..255).collect();
        chars.shuffle(&mut thread_rng());
        let chars = &chars[..thread_rng().gen_range(1..chars.len())];
        for i in 0..chars.len() {
            let mut prefix = chars[i]
                .to_bytes()
                .as_slice()
                .repeat(thread_rng().gen_range(1..8));
            for i in 0..chars.len() {
                let level2_prefix = chars[i]
                    .to_bytes()
                    .as_slice()
                    .repeat(thread_rng().gen_range(1..8));
                prefix.extend(level2_prefix);
                for _ in 0..=u8::MAX {
                    let hi: usize = thread_rng().gen_range(0..8);
                    let suffix: Vec<u8> = (0..hi)
                        .map(|_| chars[thread_rng().gen_range(0..chars.len())])
                        .collect();
                    let mut string: Vec<u8> = prefix.clone();
                    string.extend(&suffix[..]);
                    if !existing.insert(string.clone()) {
                        continue;
                    }
                    test_fn(art, string);
                    if existing.len() >= 70 {
                        return;
                    }
                }
            }
        }
    }
}
