use std::iter;

use criterion::{black_box, criterion_group, criterion_main, Criterion, BenchmarkId, Throughput};
use bromberg_sl2::*;
use sha3::{Digest, Sha3_512};

// This isjust stolen straight from the Criterion documentation
fn from_elem(c: &mut Criterion) {
    static KB: usize = 1024;

    let mut group = c.benchmark_group("from_elem");
    for size in [KB, 2 * KB, 4 * KB, 8 * KB, 16 * KB].iter() {
        group.throughput(Throughput::Bytes(*size as u64));
        group.bench_with_input(BenchmarkId::new("bromberg", size), size, |b, &size| {
            b.iter(|| black_box(iter::repeat(5u8).take(size).collect::<Vec<u8>>().bromberg_hash()));
        });
    }
    for size in [KB, 2 * KB, 4 * KB, 8 * KB, 16 * KB].iter() {
        group.throughput(Throughput::Bytes(*size as u64));
        group.bench_with_input(BenchmarkId::new("sha", size), size, |b, &size| {
            b.iter(|| {
                let mut hasher = Sha3_512::new();
                black_box(hasher.update(iter::repeat(5u8).take(size).collect::<Vec<u8>>()));
                black_box(hasher.finalize());
            });
        });
    }
    group.finish();
}

criterion_group!(benches, from_elem);
criterion_main!(benches);
