# Aocla Oxidized Edition

Aocla (Advent of Code inspired Language) is a toy stack-based programming language made by [antirez](https://github.com/antirez).

## What's the purpose of this repository?

Well, it is not just another [RIIR](https://transitiontech.ca/random/RIIR), but rather rewrite to higher level language for better expandability.

I love the idea of small languages, the idea of making **anything** you want with just some really basic tools the language gives you.
**C** is a quite simple language, but its simplicity is sometimes *really* annoying.
When you have to use `malloc` along with `free` and keep track of memory allocations... It isn't the best tool for daily programming usage.

## Overview

Aocla is a quite simple language. Current implementation has 6 datatypes:
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
    [$n $a $i @ =] [
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
- [ ] Every original procedure (likely won't happen)
- [ ] Commentaries (they were working, but recently i rewrote whole parser with [nom](https://github.com/rust-bakery/nom) library and broke them)

What i *would* like to add:
- [ ] Better-looking REPL (with history and syntax highlighting)
- [ ] Procedures for dealing with lists (-> (prepend), <- (append), :: (cons), @ (get by index))
- [ ] Procedures for dealing with strings (maybe same set like lists?)
- [ ] C or/and Rust interoperability. Why not?
