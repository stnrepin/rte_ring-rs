# rte_ring

Ring library from [DPDK] ported to Rust.

Based on DPDK `21.11.0`.

[DPDK]: http://www.dpdk.org/

## Features

-   FIFO
-   Maximum size is fixed, the pointers are stored in a table
-   Lockless implementation
-   Multi-consumer or single-consumer dequeue
-   Multi-producer or single-producer enqueue
-   Bulk dequeue -- Dequeues the specified count of objects if successful;
    otherwise fails
-   Bulk enqueue -- Enqueues the specified count of objects if successful;
    otherwise fails
-   TBD ~Burst dequeue -- Dequeue the maximum available objects if the specified
    count cannot be fulfilled~
-   TBD ~Burst enqueue -- Enqueue the maximum available objects if the specified
    count cannot be fulfilled~

## Example

```rust
use rte_ring::*;

// A size should be a power of two (real size is `2^n-1`).
// Use `flags` to make one or both ends of the ring not thread-safe.
let r = Ring::<i32>::new(8, flags::NONE).unwrap();

r.enqueue(1);
r.enqueue_bulk(&[2, 3]);
assert_eq!(r.count(), 3);

let x = r.dequeue().unwrap();
assert_eq!(x, 1);

let mut xs = [0; 2];
r.dequeue_bulk(&mut xs);
assert_eq!(vec![2, 3], xs);

assert_eq!(r.count(), 0);
```

<!-- Also, see [`examples/`](./examples/) for more complex examples. -->

## Internals

TBD. For now see [Programmer's Guide from DPDK][1].

[1]: http://doc.dpdk.org/guides-21.11/prog_guide/ring_lib.html

## TODO

-   Docs.
-   Multithread tests, loom.
-   Bulk-functions (only interface, algorithm already supports).
-   Refactor, split implementation, separate interface from
    implementation (traits?).
-   More examples.
-   Benchmarks, compare to DPDK.

## License

BSD 3-Clause license
