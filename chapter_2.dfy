method ex26a (x: int) returns (x': int)
  requires -128 <= x < 0
  ensures 2 <= x' < 130
{ x' := 1 - x; }

method ex26b (x : int , y : int) returns (y' : int)
  requires 0 <= x <= y < 100
  ensures 0 <= y' < 100
{ y' := y - x;}

predicate isEven(x :int)
{
  x % 2 == 0
}

method ex26c (x : int, y : int) returns (x' : int, y' : int)
  requires isEven(x)
  requires y < 100
  ensures isEven(y')
  ensures x' < 100
{
  x',y' := y,x;
}

method ex27a (x : int) returns (x' : int)
  ensures x' == 400 
{
  x' := 400;
}

method ex27b (x : int) returns (x' : int)
  requires !isEven(x)
  ensures isEven(x')
{
  x' := x + 3;
}

method ex27c (y : int) returns (x' : int)
  requires y <= 65
  ensures y <= x'
{
  x' := 65;
}

method ex28a (x : int, y : int) returns (b' : bool)
  requires y >= 10 || x < y
  ensures b' ==> x < y
{
  b' := y < 10;
}

method ex28b (x : int, y : int) returns (x' : int, y' : int)
  requires 0 <= x <= 50 && y <= x
  ensures 0 <= x' <= 100 && y' <= x'
{
  x',y' := 2 * x , x + y;
}

method ex28c (x : int, y : int) returns (x' : int)
  requires false
  ensures 10 <= x <= y
{
  x' := 2 * y;
}

method Inc(x: int) returns (y: int)
  requires x >= 0
  ensures y > 0
{
  y := x + 1;
}

method AddThenDouble(x: int) returns (y: int)
  requires x >= 3
  ensures y >= 10
{
  var z := x + 2;
  y := z * 2;
}

method Divide(x: int, y: int) returns (z: int)
  requires y != 0
  requires x % y == 0
  ensures z * y == x
{
  z := x / y;
}