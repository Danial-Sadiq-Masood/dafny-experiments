method InitArray<T>(a : array<T>, d: T)
    modifies a
    ensures forall i :: 0 <= i < a.Length ==> a[i] == d
{
  var n := 0;
  
  while n!= a.Length
    invariant 0 <= n <= a.Length
    invariant forall i :: 0 <= i < n ==> a[i] == d
  {
    a[n] := d;
    n := n + 1;
  }
}

method InitMatrix<T>(a : array2<T>, d : T)
  modifies a
  ensures forall i,j ::
    0 <= i < a.Length0 && 0 <=j < a.Length1 ==> a[i,j] == d
{
  var m := 0;

  while m != a.Length0
    invariant 0 <= m <= a.Length0
    invariant forall i,j :: 0 <= i < m && 0 <= j < a.Length1 ==> a[i,j] == d
    {
      var n := 0;
      while n != a.Length1
        invariant 0 <= n <= a.Length1
        invariant forall i, j ::
        0 <= i < m && 0 <= j < a.Length1 ==> a[i,j] == d
        invariant forall j :: 0 <= j < n ==> a[m,j] == d
      {
        a[m,n] := d;
        n := n + 1;
      } 
      m := m + 1;
    }
}

method IncrementArray(a : array<int>)
  modifies a
  ensures forall i :: 0 <= i < a.Length ==> a[i] == old(a[i]) + 1
{
  var n := 0;
  
  while n != a.Length
    invariant 0 <= n <= a.Length
    invariant forall i :: 0 <= i < n ==> a[i] == old(a[i]) + 1
    invariant forall i :: n <= i < a.Length ==> a[i] == old(a[i])
  {
    a[n] := a[n] + 1;
    n := n + 1;
  }
}

method CopyArray(src : array, dst : array)
  requires src.Length == dst.Length
  requires src != dst
  modifies dst
  ensures forall i :: 0 <= i < src.Length ==> dst[i] == src[i]
{
  var n := 0;
  while n != dst.Length
    invariant 0 <= n <= dst.Length
    invariant forall i :: 0 <= i < n ==> dst[i] == src[i]
  {
    dst[n] := src[n];
    n := n + 1;
  }
}