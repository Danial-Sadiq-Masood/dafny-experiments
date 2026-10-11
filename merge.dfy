predicate SortedOrdered(a : seq<int>)
{
  forall i,j :: 0 <= i < j < |a| ==> a[j] >= a[i]
}



