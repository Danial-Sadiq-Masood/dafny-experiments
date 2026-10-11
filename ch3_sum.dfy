//3.0
function F(x:int) : int
  decreases x
{
  if x < 10 then x else F(x - 1)
}

//3.1
function G(x:int) : int
  decreases x
{
  if 0 <= x then G(x - 2) else x
}

//3.2
function H(x: int) : int
  decreases x + 60
{
  if x < -60 then x else H(x - 1)
}

//3.3
function I(x: int, y: int) : int
  requires x >= 0 && y >= 0
  decreases x, y
{
  if x == 0 || y == 0 then
    12
  else if x % 2 == y % 2 then
    I(x - 1, y)
  else
    I(x, y - 1)
}

//3.4
function J(x: nat, y: nat) : int
  decreases x, y
{
  if x == 0 then
    y
  else if y == 0 then
    J(x - 1, 3)
  else
    J(x, y - 1)
}

//3.5
function K(x: nat, y: nat) : int
  decreases x, y
{
  if x == 0 then
    y
  else if y == 0 then
    J(x - 1, 3)
  else
    J(x, y - 1)
}

//3.6
function L(x: int) : int
  decreases 100 - x
{
  if x < 100 then L(x + 1) + 10 else x
}

//3.7
function G1(n: nat) : nat
  decreases n
{
  if n == 0 then 0 else n - G1(G1(n - 1))
}

//3.8
function M(x: int, b: bool): int
  decreases !b
{
  if b then x else M(x + 25, true)
}

//3.9
function N(x: int, y: int, b: bool): int
  decreases x,b
{
  if x <= 0 || y <= 0 then
    x + y
  else if b then
    N(x, y + 3, !b)
  else
    N(x - 1, y, true)
}

/*method {:axiom} RequiredStudyTime(c: nat) returns (hours: nat)
  ensures hours > 0

method Outer(a: nat, c : nat)
  decreases a,c
{
  if a != 0 {
    var b := RequiredStudyTime(a - 1);
    Inner(a - 1, b, b);
  }
}
method Inner(a: nat, original_b : nat, b: nat)
  requires original_b > 0
  decreases a,original_b,b
{
  if b == 0 {
    Outer(a, original_b - 1);
  } else {
    Inner(a, original_b, b - 1);
  }
}
*/

method RequiredStudyTime(c: nat) returns (hours: nat)

method Outer(a: nat) 
  decreases a
{
  if a != 0 {
    var b := RequiredStudyTime(a - 1);
    Inner(a - 1, b);
  }
}

method Inner(a: nat, b: nat) 
  decreases a + 1,b
{
  if b == 0 {
    Outer(a);
  } else {
    Inner(a, b - 1);
  }
}