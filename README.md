# Aocla Oxidized Edition

Aocla (Advent of Code inspired Language) is a toy stack-based programming language made by [antirez](https://github.com/antirez).

## Overview

Aocla is a quite simple language. Current implementation has 6 datatype:
 * List: `[1 2 3 "foo"]`
 * Tuple: `(x y z)`
 * Symbol: `mysymbol`, `=` or `$x`
 * Integer: `500`
 * Boolean: `#t` or `#f`
 * String: `"Hello, World!\n"`

## Examples

Example of using `while` and `if` for making some basic algorithms like finding value in list:

```aocla
[(a n)
  0 #f (i found)
  [$found not $i $a len < and] [
    [$n $a $i get =] [
      #t (found)
    ] [
      $i 1 + (i)
    ] ifelse
  ] while
  $i
] 'find proc

[1 2 3 1234 5 6 7 1000] (a)

$a 1234 find println
$a 1000 find println
```

Other examples can be found in [examples](examples/) folder

## TODO

Most parts of the original language was implemented but not everything:
- [x] Basic datatypes
- [ ] Every original procedure (unlikely won't happen)
- [ ] Commentaries (they were working, but recently i rewrote whole parser with [nom](https://github.com/rust-bakery/nom) library and broke them)

What i *would* like to add:
- [ ] Better-looking REPL (with history and syntax highlighting)
- [ ] Procedures for dealing with lists (push, pop, set, ~~get~~)
- [ ] Procedures for dealing with strings (maybe same set like lists?)
- [ ] C or/and Rust interoperability. Why not?
