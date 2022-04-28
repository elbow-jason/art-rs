use art_tree::Art;
use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use rand::prelude::*;
use rand::{thread_rng, Rng};
use std::collections::HashSet;
use std::time::{Duration, Instant};

pub fn insert(c: &mut Criterion) {
    let mut rng = thread_rng();
    let mut group = c.benchmark_group("modification");
    group.throughput(Throughput::Elements(1));
    group.bench_function("seq_insert", |b| {
        let mut tree = Art::new();
        let mut key = 0u64;
        b.iter(|| {
            tree.insert(key, key);
            key += 1;
        })
    });

    group.bench_function("seq_upsert", |b| {
        let mut tree = Art::new();
        let mut key = 0u64;
        b.iter(|| {
            tree.upsert(key, key);
            key += 1;
        })
    });

    let keys = gen_keys(&mut rng, 3, 2, 3);

    group.bench_function("rand_insert", |b| {
        let mut tree = Art::new();
        let i = rng.gen_range(0..keys.len());
        b.iter(|| {
            tree.insert(&keys[i][..], &keys[i][..]);
        })
    });

    let ks = gen_keys(&mut rng, 3, 2, 3);

    group.bench_function("rand_upsert", |b| {
        let mut tree = Art::new();
        let i = rng.gen_range(0..ks.len());
        b.iter(|| {
            tree.upsert(&ks[i][..], &ks[i][..]);
        })
    });
    group.finish();
}

pub fn delete(c: &mut Criterion) {
    let mut rng = thread_rng();
    let mut group = c.benchmark_group("modification");
    group.throughput(Throughput::Elements(1));
    group.bench_function("remove", |b| {
        let mut tree = Art::new();
        b.iter_custom(|iters| {
            for i in 0..iters {
                tree.insert(i, i);
            }
            let start = Instant::now();
            for i in 0..iters {
                tree.remove(&i);
            }
            start.elapsed()
        })
    });

    let keys = gen_keys(&mut rng, 3, 2, 3);

    group.bench_function("rand_remove", |b| {
        let mut tree = Art::new();
        for key in keys.iter() {
            tree.upsert(&key[..], &key[..]);
        }
        let key = &keys[rng.gen_range(0..keys.len())];
        b.iter(|| {
            tree.remove(&&key[..]);
        })
    });
    group.finish();
}

pub fn access(c: &mut Criterion) {
    let mut rng = thread_rng();
    let mut group = c.benchmark_group("access");
    group.throughput(Throughput::Elements(1));
    for size in [100u64, 1000, 10_000, 100_000, 1_000_000, 5_000_000] {
        group.bench_with_input(BenchmarkId::new("rand_get", size), &size, |b, size| {
            let mut tree = Art::new();
            for i in 0..*size {
                tree.insert(i, i);
            }
            let key = rng.gen_range(0..*size);
            b.iter(|| {
                tree.get(&key);
            })
        });
    }

    for size in [100u64, 1000, 10_000, 100_000, 1_000_000, 5_000_000] {
        group.bench_with_input(
            BenchmarkId::new("rand_get_half_misses", size),
            &size,
            |b, size| {
                let mut tree = Art::new();
                for i in 0..*size {
                    tree.insert(i, i);
                }
                let key = rng.gen_range(0..(*size * 2));
                b.iter(|| {
                    tree.get(&key);
                })
            },
        );
    }

    for size in [100u64, 1000, 10_000, 100_000, 1_000_000, 5_000_000] {
        group.bench_with_input(BenchmarkId::new("seq_get", size), &size, |b, size| {
            let mut tree = Art::new();
            for i in 0..*size {
                tree.insert(i, i);
            }
            let mut key = 0u64;
            b.iter(|| {
                tree.get(&key);
                key += 1;
            })
        });
    }
    group.finish();
}

pub fn iter(c: &mut Criterion) {
    let mut rng = rand::thread_rng();
    let mut group = c.benchmark_group("iteration");
    group.throughput(Throughput::Elements(1));
    for size in [100u64, 1000, 10_000, 100_000, 1_000_000, 5_000_000] {
        group.bench_with_input(BenchmarkId::new("iter_u64", size), &size, |b, size| {
            let mut tree = Art::new();
            for i in 0..*size {
                tree.insert(i, i);
            }
            let mut it = tree.iter();
            b.iter(|| match it.next() {
                Some(_) => {}
                None => it = tree.iter(),
            })
        });
    }

    let outer_smalls: Vec<String> = gen_keys(&mut rng, 2, 2, 2);

    group.bench_function("string_len_6", |b| {
        let mut tree = Art::new();
        for (i, bs) in outer_smalls.iter().enumerate() {
            tree.insert(bs, i);
        }
        let mut it = tree.iter();
        b.iter(|| match it.next() {
            Some(_) => {}
            None => it = tree.iter(),
        })
    });

    let outer_mids: Vec<String> = gen_keys(&mut rng, 4, 4, 3);

    group.bench_function("string_len_11", |b| {
        let mut tree = Art::new();
        for (i, bs) in outer_mids.iter().enumerate() {
            tree.insert(bs, i);
        }
        let mut it = tree.iter();
        b.iter(|| match it.next() {
            Some(_) => {}
            None => it = tree.iter(),
        })
    });

    let outer_larges: Vec<String> = gen_keys(&mut rng, 8, 6, 6);

    group.bench_function("string_len_20", |b| {
        let mut tree = Art::new();
        for (i, bs) in outer_larges.iter().enumerate() {
            tree.insert(bs, i);
        }
        let mut it = tree.iter();
        b.iter(|| match it.next() {
            Some(_) => {}
            None => it = tree.iter(),
        })
    });
    group.finish();
}

// fn random_key<const S: usize>(r: &mut ThreadRng) -> [u8; S] {
//     let mut bytes = [0u8; S];
//     r.fill_bytes(&mut bytes);
//     bytes
// }

fn gen_keys(r: &mut ThreadRng, l1_prefix: usize, l2_prefix: usize, suffix: usize) -> Vec<String> {
    let mut keys = HashSet::new();
    let chars: Vec<char> = ('a'..='z').collect();
    for i in 0..chars.len() {
        let level1_prefix = chars[i].to_string().repeat(l1_prefix);
        for i in 0..chars.len() {
            let level2_prefix = chars[i].to_string().repeat(l2_prefix);
            let key_prefix = level1_prefix.clone() + &level2_prefix;
            for _ in 0..=u8::MAX {
                let suffix: String = (0..suffix)
                    .map(|_| chars[r.gen_range(0..chars.len())])
                    .collect();
                let string = key_prefix.clone() + &suffix;
                keys.insert(string.clone());
            }
        }
    }

    let mut res: Vec<String> = keys.drain().collect();
    res.shuffle(&mut thread_rng());
    res
}

fn cfg() -> Criterion {
    Criterion::default()
        .warm_up_time(Duration::from_millis(500))
        .measurement_time(Duration::from_millis(1500))
}

// criterion_group!(config(), mods, insert);
// criterion_group!(dels, delete);
// criterion_group!(gets, access);
// criterion_group!(iters, iter);

criterion_group! {
    name = mods;
    config = cfg();
    targets = insert
}

criterion_group! {
    name = dels;
    config = cfg();
    targets = delete
}

criterion_group! {
    name = gets;
    config = cfg();
    targets = access
}

criterion_group! {
    name = iters;
    config = cfg();
    targets = iter
}

criterion_main!(mods, dels, gets, iters);
