datatype List<T> = Nil | Cons(head : T, tail : List<T>)

function Length<T>(xs: List<T>): nat {
  match xs
  case Nil => 0
  case Cons(_, tail) => 1 + Length(tail)
}

function Length'<T>(xs : List<T>): nat {
  if xs == Nil then 0 else 1 + Length'(xs.tail)
}

lemma {:induction false} SameLength<T>(xs : List<T>)
  ensures Length(xs) == Length'(xs) {
  match xs
  case Nil => {
    //Length(xs) == Length'(xs) == 0
    assert Length(xs) == Length'(xs);
  }
  case Cons(head, tail) => {
    calc {
      Length(xs);
    ==
      1 + Length(tail);
    ==
      { SameLength(tail);}
      1 + Length'(tail);
    ==
      Length'(xs);
    }
  }
}

function Snoc<T>(xs: List<T>, y: T): List<T> {
  match xs
  case Nil => Cons(y, Nil)
  case Cons(x, tail) => Cons(x, Snoc(tail, y))
}

lemma {:induction false} LengthSnoc<T>(xs: List<T>, x: T)
  ensures Length(Snoc(xs, x)) == Length(xs) + 1
{
  match xs
  case Nil => {
    assert Length(Snoc(xs,x)) == 1;
    assert Length(xs) == 0;
    assert Length(Snoc(xs,x)) == Length(xs) + 1;
  }
  case Cons(head, tail) => {
    calc {
      Length(Snoc(xs,x));
    ==
      Length(Cons(head, Snoc(tail,x)));
    ==
      1 + Length(Snoc(tail,x));
    ==
      {
        LengthSnoc(tail,x);
      }
      1 + (Length(tail) + 1);
    ==
      {
        assert Length(xs) == Length(tail) + 1;
      }
      Length(xs) + 1;
    }
  }
}

function Append<T>(xs: List<T>, ys: List<T>): List<T>
  ensures Length(Append(xs, ys)) == Length(xs) + Length(ys)
{
  match xs
  case Nil => ys
  case Cons(x, tail) => Cons(x, Append(tail, ys))
}

lemma {:induction false} SnocAppend<T>(xs : List<T>, y : T)
  ensures Snoc(xs, y) == Append(xs, Cons(y, Nil))
{
  match xs
  case Nil => {
    calc {
      Snoc(xs,y);
    ==
      Cons(y,Nil);
    ==
      Append(xs, Cons(y, Nil));
    }
  }
  case Cons(head, tail) => {
    calc {
      Snoc(xs,y);
    ==
      Cons(head, Snoc(tail, y));
    ==
      {SnocAppend(tail,y);}
      Cons(head, Append(tail,Cons(y,Nil)));
    ==
      Append(xs, Cons(y, Nil));
    }
  }
}

lemma {:induction false} AppendNil<T>(xs: List<T>)
  ensures Append(xs, Nil) == xs
{
  match xs
  case Nil => {
    calc {
      Append(xs, Nil);
    ==
      Nil;
    ==
      xs;
    }
  }
  case Cons(head, tail) => {
    calc{
      Append(xs, Nil);
    ==
      Cons(head, Append(tail, Nil));
    ==
      {AppendNil(tail);}
      Cons(head, tail);
    ==
      xs;
    }
  }
}


function Take<T>(xs: List<T>, n : nat) : List<T>
  requires n <= Length(xs)
{
  if n == 0 then Nil else Cons(xs.head, Take(xs.tail,n - 1))
}

function Drop<T>(xs: List<T>, n: nat): List<T>
  requires n <= Length(xs)
{
  if n == 0 then xs else Drop(xs.tail, n - 1)
}


lemma {:induction false} AppendTakeDrop<T>(xs: List<T>, n: nat)
  requires n <= Length(xs)
  ensures Append(Take(xs, n), Drop(xs, n)) == xs
{
  match xs
  case Nil => {
    assert n == 0;
    calc {
      Append(Take(xs, n), Drop(xs, n));
    ==
      Append(Nil, Nil);
    ==
      Nil;
    }
  }
  case Cons(head, tail) => {
    if n == 0{
      calc{
        Append(Take(xs, n), Drop(xs, n));
      ==
        Append(Nil, xs);
      ==
        xs;
      }
    }else{
      calc{
        Append(Take(xs, n), Drop(xs, n));
      ==
        Append(Cons(xs.head, Take(tail,n - 1)), Drop(tail, n - 1));
      ==
        Cons(xs.head, Append(Take(tail,n - 1),Drop(tail, n - 1)));
      ==
        {
          AppendTakeDrop(tail, n - 1);
        }
        Cons(xs.head, tail);
      ==
        xs;
      }
    }
  }
}

function At<T>(xs : List<T>, i : nat) : T
  requires i < Length(xs)
{
  if i == 0 then xs.head else At(xs.tail, i - 1)
}

lemma {:induction false} AtDropHead<T>(xs: List<T>, i: nat)
  requires i < Length(xs)
  ensures Drop(xs,i).Cons? ==> At(xs, i) == Drop(xs, i).head
{
  if(Drop(xs,i).Cons?){
    match xs
    case Nil => {
      //imposible
    }
    case Cons(head, tail) => {
      if i == 0{
        calc{
          At(xs, i);
        ==
          head;
        ==
          {assert Drop(xs,0) == xs;}
          Drop(xs, 0).head;
        }
      }else{
        calc{
          At(xs,i);
        ==
          At(tail, i - 1);
        ==
          {AtDropHead(tail, i - 1);}
          Drop(tail, i - 1).head;
        ==
          Drop(xs, i).head;
        }
      }
    }
  }
}

function Find<T(==)>(xs: List<T>, y: T): nat
  ensures Find(xs, y) <= Length(xs)
{
  match xs
  case Nil => 0
  case Cons(x, tail) =>
    if x == y then 0 else 1 + Find(tail, y)
}

lemma {:induction false} AtFind<T>(xs: List<T>, y: T)
  ensures Find(xs, y) == Length(xs) || At(xs, Find(xs, y)) == y
{
  match xs
  case Nil => {
    calc{
      Find(xs, y);
    ==
      0;
    ==
      Length(xs);
    }
  }
  case Cons(head, tail) => {
    if head == y{
      assert Find(xs,y) == 0;
      calc {
        At(xs, 0);
      ==
        y;
      ==
        At(xs, Find(xs, y));
      }
    }else{
      AtFind(tail, y);
      assert Find(tail, y) == Length(tail) || At(tail, Find(tail, y)) == y;
      if(Find(tail, y) == Length(tail)){
        calc{
          Find(xs, y);
        ==
          Length(tail) + 1;
        ==
          Length(xs);
        }
      }else{
        calc{
          At(tail, Find(tail, y));
        ==
          {assert head != y;}
          At(Cons(head,tail), Find(Cons(head, tail), y));
        ==
          At(xs, Find(xs, y));
        }
      }
    }
  }
}

function ReverseAux<T>(xs : List<T>, acc : List<T>) : List<T>
{
  match xs
  case Nil => acc
  case Cons(head, tail) => ReverseAux(tail, Cons(head,acc))
}

ghost predicate Ordered(xs: List<int>) {
  match xs
  case Nil => true
  case Cons(x, Nil) => true
  case Cons(x, Cons(y, _)) => x <= y && Ordered(xs.tail)
}

lemma AllOrdered(xs: List<int>, i: nat, j: nat)
  requires Ordered(xs) && i <= j < Length(xs)
  ensures At(xs, i) <= At(xs, j)
{
  match xs
  case Nil => {
    //redundant
  }
  case Cons(head, Nil) => {

  }
  case Cons(head, Cons(y, tail)) => {
    if i == j{
      assert At(xs, i) <= At(xs, j);
    }else{
      if i == 0{
        calc{
          At(xs, i);
        ==
          head;
        <=
          y;
        <=
          {AllOrdered(xs.tail, 0, j-1);}
          At(xs,j);
        }
      }else{
        {AllOrdered(xs.tail, i-1, j-1);}
        assert At(xs, i) <= At(xs, j);
      }
    }
  }
}

ghost function Count<T>(xs: List<T>, p: T): nat {
  match xs
  case Nil => 0
  case Cons(x, tail) =>
    (if x == p then 1 else 0) + Count(tail, p)
}

ghost function Project(xs: List<int>, p: int): List<int> {
  match xs
  case Nil => Nil
  case Cons(x, tail) =>
    if x == p then Cons(x, Project(tail, p)) else Project(tail, p)
}

lemma {:induction false} CountProjectEqualsCount(xs : List<int>, p : int)
  ensures Count(Project(xs,p),p) == Count(xs,p)
{
  match xs
  case Nil => {

  }
  case Cons(head, tail) => {
    CountProjectEqualsCount(tail,p);
    var additionalPInCons := if head == p then 1 else 0;

    calc {
      Count(Project(xs,p),p);
    ==
      Count(Project(tail,p), p) + additionalPInCons;
    ==
      Count(tail,p) + additionalPInCons;
    ==
      Count(xs,p);
    }
  }
}

lemma {:induction false} SameCountP(xs: List<int>, ys : List<int>, p: int)
  requires Project(xs,p) == Project(ys,p)
  ensures Count(xs,p) == Count(ys,p)
{
  calc{
    Count(xs,p);
  ==
    {CountProjectEqualsCount(xs,p);}
    Count(Project(xs,p),p);
  ==
    Count(Project(ys,p),p);
  ==
    {CountProjectEqualsCount(ys,p);}
    Count(ys,p);
  }
}

function Insert(y : int, xs : List<int>) : List<int> {
  match xs
  case Nil => Cons(y,Nil)
  case Cons(head, tail) => if y < head then Cons(y, xs) else Cons(head, Insert(y, tail))
}

function InsertionSort(xs : List<int>) : List<int> {
  match xs
  case Nil => Nil
  case Cons(head, tail) => Insert(head, InsertionSort(tail))
}

lemma InsertOrdered(y: int, xs: List<int>)
  requires Ordered(xs)
  ensures Ordered(Insert(y, xs))
{
  match xs
  case Nil => {
    calc {
      Ordered(Insert(y, xs));
    ==
      Ordered(Cons(y,Nil));
    ==
      true;
    }
  }
  case Cons(x, tail) => {
    if y < x{
      calc{
        Ordered(Insert(y, xs));
      ==
        Ordered(Cons(y,xs));
      ==
        true;
      }
    }else{
      calc{
        Ordered(Insert(y, xs));
      ==
        Ordered(Cons(x, Insert(y, tail)));
      ==
        {InsertOrdered(y,tail);}
        true;
      }
    }
  }
}

function Split(xs: List, n: nat): (List, List)
  requires n <= Length(xs)
  ensures var (left, right) := Split(xs,n);
          Length(left) == n &&
          Length(right) == Length(xs) - n &&
          Append(left,right) == xs
{
  if n == 0 then
    (Nil, xs)
  else
    var (l,r) := Split(xs.tail, n - 1);
    (Cons(xs.head, l), r)
}

function Merge(xs : List<int>, ys : List<int>) : List<int>
{
  match (xs,ys)
  case (Nil, Nil) => Nil
  case (Nil, Cons(_,_)) => ys
  case (Cons(_,_), Nil) => xs
  case (Cons(x, xtail), Cons(y, ytail)) =>
    if x <= y then
      Cons(x, Merge(xtail, ys))
    else
      Cons(y, Merge(xs, ytail))
}

lemma MergeOrdered(xs : List<int>, ys : List<int>)
  requires Ordered(xs) && Ordered(ys)
  ensures Ordered(Merge(xs,ys))
{
  match (xs,ys)
  case (Nil,Nil) => {
    assert Ordered(Merge(xs,ys));
  }
  case (xs,Nil) => {
    assert Ordered(Merge(xs,ys));
  }
  case (Nil,ys) => {
    assert Ordered(Merge(xs,ys));
  }
  case (Cons(x, xtail), Cons(y, ytail)) => {
    if x <= y{
      var res := Cons(x, Merge(xtail, ys));
      MergeOrdered(xtail,ys);
      assert Ordered(Cons(x, Merge(xtail, ys)));
    }else{
      var res := Cons(y, Merge(xs, ytail));
      MergeOrdered(xs,ytail);
      assert Ordered(Cons(y, Merge(xs, ytail)));
    }
  }
}

function MergeSortAux(xs : List<int>, len : nat) : List<int>
  requires len == Length(xs)
  decreases len
{
  if len < 2 then
    xs
  else
    var (left, right) := Split(xs, len/2);
    Merge(MergeSortAux(left, len/2),
          MergeSortAux(right, len - len/2))
}

lemma {:induction false} MergeSortAuxOrdered(xs: List<int>, len: nat)
  requires len == Length(xs)
  ensures Ordered(MergeSortAux(xs, len))
  decreases len
{
  if len < 2{
    var res := MergeSortAux(xs,len);
    assert Ordered(res);
  }else{
    var (left, right) := Split(xs, len/2);
    calc{
      MergeSortAux(xs, len);
    ==
      Merge(MergeSortAux(left, len/2),
            MergeSortAux(right, len - len/2));
    }
    MergeSortAuxOrdered(left, len/2);
    MergeSortAuxOrdered(right, len - len/2);

    assert Ordered(MergeSortAux(left, len/2));
    assert Ordered(MergeSortAux(right, len - len/2));

    //Show merge ordered list is ordered
    MergeOrdered(MergeSortAux(left, len/2), MergeSortAux(right, len - len/2));

    assert Ordered(Merge(MergeSortAux(left, len/2), MergeSortAux(right, len - len/2)));
  }
}

lemma ProjectionSnocConsP(xs : List<int>, p : int)
  ensures Cons(p,Project(xs,p)) == Snoc(Project(xs,p),p)
{

}

lemma ProjectConsHeadPAsSnoc(xs : List<int>, p : int)
  requires !xs.Nil?
  ensures xs.head == p ==> Snoc(Project(xs.tail,p), p) == Project(xs,p)
{
  if xs.head == p {
    ProjectionSnocConsP(xs.tail,p);
    assert Snoc(Project(xs.tail,p), p) == Cons(p,Project(xs.tail,p));
  }
}

/*lemma {:induction false} MergeSameElements(xs : List<int>, ys : List<int>, p : int)
  requires Ordered(xs) && Ordered(ys)
  ensures Project(Merge(xs,ys),p) == Append(Project(xs,p),Project(ys,p))
{
  match (xs,ys)
  case (Nil,Nil) => {
    assert Project(Merge(xs,ys),p) == Append(Project(xs,p),Project(ys,p));
  }
  case (xs,Nil) => {
    assert Project(ys,p) == Nil;
    calc{
      Project(Merge(xs,ys),p);
    ==
      Project(Merge(xs,Nil),p);
    ==
      Project(xs,p);
    ==
      {AppendNil(Project(xs,p));}
      Append(Project(xs,p), Nil);
    ==
      Append(Project(xs,p), Project(ys,p));
    }
  }
  case (Nil,ys) => {
    assert Project(xs,p) == Nil;
    calc{
      Project(Merge(xs,ys),p);
    ==
      Project(Merge(ys,Nil),p);
    ==
      Project(ys,p);
    ==
      {AppendNil(Project(ys,p));}
      Append(Nil,Project(ys,p));
    ==
      Append(Project(xs,p), Project(ys,p));
    }
  }
  case (Cons(x, xtail), Cons(y, ytail)) => {
    if x <= y {
      calc{
        Project(Merge(xs,ys),p);
      ==
        Project(Cons(x, Merge(xtail, ys)),p);
      ==
        if x == p then Cons(x, Project(Merge(xtail, ys), p)) else Project(Merge(xtail, ys), p);
      ==
        {MergeSameElements(xtail,ys, p);}
        if x== p then Cons(x, Append(Project(xtail,p),Project(ys,p))) else Append(Project(xtail,p),Project(ys,p));
      ==
        Append(Project(xs,p),Project(ys,p));
      }
    }else{
      calc{
        Project(Merge(xs,ys),p);
      ==
        Project(Cons(y, Merge(xs, ytail)),p);
      ==
        if y == p then Cons(p, Project(Merge(xs, ytail), p)) else Project(Merge(xs,ytail), p);
      ==
        {MergeSameElements(xs,ytail, p);}
        if y == p then Cons(p, Append(Project(xs,p),Project(ytail,p))) else Append(Project(xs,p),Project(ytail,p));
      ==
        {
          calc {
            Cons(p, Project(Merge(xs,ytail),p));
          ==
            {ProjectionSnocConsP(Project(Merge(xs,ytail),p),p);}
            Snoc(Project(Merge(xs,ytail),p),p);
          }
        }
      }
    }
  }
}*/