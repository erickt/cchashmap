Cache-Conscious Hashmap
=======================

> This is in development and is probably buggy and very unsafe.

This is a work in progress implementation of the Cache-Conscious Hashmap, as
described by Askitis and Zobel in [Cache-Conscious Collision Resolution in
String Hash Tables](http://goanna.cs.rmit.edu.au/~jz/fulltext/spire05.pdf).
This algorithm optimizes for strings by storing the keys and values in a
contiguous array. In the best case, the overhead required for pointers is
reduced by a factor around 50, to less than two bits per string.
