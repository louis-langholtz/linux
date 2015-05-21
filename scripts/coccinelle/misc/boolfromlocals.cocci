/// Refactor local boolean variables to use bool type
///
//# This semantic patch code originally came from the LKML email archive
//# post at https://lkml.org/lkml/2014/12/17/222 from Quentin Lambert dated
//# Wed, 17 Dec 2014. It has been modified from that original code.
//

/* match all explicit boolean functions */
@boolean_function@
identifier fbool;
typedef bool;
@@

bool fbool(...) {
...
}

/* match variables eligible for boolean conversion */
@eligible_var exists@
identifier f, boolean_function.fbool;
typedef u1, u2, u4, u8, u16, u32;
local idexpression {int, u8, u1, u2, u4, u16, u32, char} x;
identifier xname;
expression e1, e2;
position p;
@@


f@p(...) {
...when any
(
  x@xname = 1;
|
  x@xname = 0;
|
  x@xname = (e1) ? 0 : 1;
|
  x@xname = (e2) ? 1 : 0;
|
  x@xname = fbool(...);
|
  x@xname = fbool(...);
|
  x@xname = e1 && ...
|
  x@xname = e1 || ...
|
  x@xname = e1 == e2
|
  x@xname = e1 != e2
|
  x@xname = e1 < e2
|
  x@xname = e1 <= e2
|
  x@xname = e1 > e2
|
  x@xname = e1 >= e2
)
...when any
}

/* match all acceptable complex assignement */
@valid_assign exists@
identifier eligible_var.f, boolean_function.fbool;
local idexpression {int, u8, u1, u2, u4, u16, u32, char} eligible_var.x;
expression e1, e2;
position p;
@@

f(...) {
...when any
(
  x@p = (e1) ? 0 : 1;
|
  x@p = (e1) ? 1 : 0;
|
  x@p = fbool(...);
|
  x@p = e1 && ...
|
  x@p = e1 || ...
|
  x@p = e1 == e2
|
  x@p = e1 != e2
|
  x@p = e1 < e2
|
  x@p = e1 <= e2
|
  x@p = e1 > e2
|
  x@p = e1 >= e2
)
...when any
}

/* match any expression where x is used as an int */
@badvar1 exists@
identifier eligible_var.f;
local idexpression {int, u8, u1, u2, u4, u16, u32, char} eligible_var.x;
expression e1 != {0, 1}, e2;
position p != {valid_assign.p};
@@

f(...) {
...when any
(
  x@p = e1;
|
  x += e2
|
  e2 += x
|
  x *= e2
|
  e2 *= x
|
  x -= e2
|
  e2 -= x
|
  x /= e2
|
  e2 /= x
|
  e2 %= x
|
  x %= e2
|
  x &= e2
|
  e2 &= x
|
  x |= e2
|
  e2 |= x
|
  x ^= e2
|
  e2 ^= x
|
  x <<= e2
|
  e2 <<= x  
|
  x >>= e2
|
  e2 >>= x  
|
  x++
|
  ++x
|
  x--
|
  --x
|
  x + e2
|
  x - e2
|
  e2 - x
|
  x & e2
|
  x | e2
|
  x * e2
|
  x / e2
|
  e2 / x
|
  x % e2
|
  e2 % x
|
  ~x
|
  e2 ^ x
|
  x ^ e2
|
  x << e2
|
  e2 << x
|
  x >> e2
|
  e2 >> x
|
  &x
)
...when any
}


@depends on !badvar1@
identifier eligible_var.f;
local idexpression {int, u8, u1, u2, u4, u16, u32, char} eligible_var.x;
identifier eligible_var.xname;
type t;
expression e;
@@

f(...) {
...
(
- t xname = 0;
+ bool xname = false;
|
- t xname = 1;
+ bool xname = true;
|
- t xname;
+ bool xname;
)
<...
(
x =
- 1
+ true
|
x =
- 0
+ false
|
- x = (e) ? 1 : 0
+ x = (e) ? true : false
|
- x = (e) ? 0 : 1
+ x = (e) ? false : true
)
...>

}
