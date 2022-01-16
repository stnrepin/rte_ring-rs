# rte_ring

Ring library from [DPDK] ported to Rust.

Based on DPDK `21.11.0`.

[DPDK]: http://www.dpdk.org/


## Features

* FIFO
* Maximum size is fixed, the pointers are stored in a table
* Lockless implementation
* Multi-consumer or single-consumer dequeue
* Multi-producer or single-producer enqueue
* Bulk dequeue -- Dequeues the specified count of objects if successful; otherwise fails
* Bulk enqueue -- Enqueues the specified count of objects if successful; otherwise fails
* Burst dequeue -- Dequeue the maximum available objects if the specified count cannot be fulfilled
* Burst enqueue -- Enqueue the maximum available objects if the specified count cannot be fulfilled

## Internals

TBD. For now see [Programmer's Guide from DPDK][1].

[1]: http://doc.dpdk.org/guides-21.11/prog_guide/ring_lib.html

## Licence

BSD-3-Clause license

