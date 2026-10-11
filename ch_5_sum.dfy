function More(x: int): int {
  if x <= 0 then 1 else More(x - 2) + 3
}

lemma {:induction false} Increasing(x: int)
  ensures x < More(x) 
{
  if x <= 0 {

  }else{
    calc {
      More(x);
      == More(x - 2) + 3;
      > {Increasing(x - 2);}
        x - 2 + 3;
      == x + 1;
      > x;
    }
  }
}

function Reduce(m: nat, x: int): int {
  if m == 0 then x else Reduce(m / 2, x + 1) - m
}

lemma {:induction false} ReduceUpperBound(m: nat, x: int)
  ensures Reduce(m,x) <= x
{
  if m == 0 {

  } else {
    calc {
      Reduce(m,x);
    ==
      Reduce(m / 2, x + 1) - m;
    <=
      {
        ReduceUpperBound(m/2, x + 1);
        assert Reduce(m/2,x + 1) <= x + 1;
      }
      x + 1 - m;
    <= 
      {
        assert 0 < m;
      }
      x;
    }
  }
}
