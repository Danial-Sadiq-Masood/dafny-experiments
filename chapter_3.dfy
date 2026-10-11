function SumTo(arr: array<int>, n: int): int
  requires 0 <= n <= arr.Length
  reads arr
{
  if n == 0 then 0 else SumTo(arr, n - 1) + arr[n - 1]
}

function SumToPlus100(arr : array<int>, n: int): int
  requires 0 <= n <= arr.Length
  reads arr
{
  if n == 0 then 100 else SumTo(arr, n) + 100
}

method Sum(arr: array<int>) returns (s: int)
    ensures s == SumTo(arr, arr.Length)
{
  var i := 0;
  s := 0;

  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant s == SumTo(arr, i)
  {
    s := s + arr[i];
    i := i + 1;
  }
}

method SumTo2(arr: array<int>) returns (s: int)
    ensures s == SumToPlus100(arr, arr.Length)
{
  var i := 0;
  s := 0;

  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant s == SumTo(arr, i)
  {
    s := s + arr[i];
    i := i + 1;
  }

  s := s + 100;
}

method Abs(x: int) returns (y: int)
  ensures y >= 0
  ensures y == x || y == -x
{
  y := if x < 0 then -x else x;
}

method AllNonNegative(arr: array<int>) returns (ok: bool)
  ensures ok <==> (forall i :: 0 <= i < arr.Length ==> arr[i] >= 0)
{
  var i := 0;
  ok := true;

  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant ok <==> (forall j :: 0 <= j < i ==> arr[j] >= 0)
    {
      ok := ok && arr[i] >= 0;
      i := i + 1;
    }
}

method FindElem(arr: array<int>, x: int) returns (index: int)
  ensures -1 <= index < arr.Length
  ensures index == -1 || arr[index] == x
{
  var i := 0;
  index := -1;

  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant forall j :: 0 <= j < i ==> arr[j] != x
  {
    if arr[i] == x {
      index := i;
      break;
    }
    i := i + 1;
  }
}

method FindAllElems(arr: array<int>, x: int) returns (indices: seq<int>)
  ensures forall i :: 0 <= i < |indices| ==> 0 <= indices[i] < arr.Length
  ensures forall i :: 0 <= i < |indices| ==> arr[indices[i]] == x
  ensures forall i :: 0 <= i < arr.Length && arr[i] == x ==> i in indices
{
  var i := 0;
  indices := [];

  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant forall j :: 0 <= j < |indices| ==> 0 <= indices[j] < arr.Length
    invariant forall k :: 0 <= k < i && arr[k] == x ==> k in indices
    invariant forall j :: 0 <= j < |indices| ==> arr[indices[j]] == x
    {
      if arr[i] == x {
        indices := indices + [i];
      }
      i := i + 1;
    }
}