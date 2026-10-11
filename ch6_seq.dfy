datatype List<T> = Nil | Cons(head: T, tail: List<T>)

function Length<T>(l : List<T>) : nat
{
  match l
  case Nil => 0
  case Cons(h, tail) => 1 + Length(tail)
}

function Length1<T>(l : List<T>) : nat
{
  if l == Nil then 0 else 1 + Length1(l.tail)
}

lemma SameLength<T>(l : List<T>)
  ensures Length(l) == Length1(l)
{

}


function Snoc<T>(xs : List<T>, y : T) : List<T>
{
  match xs
  case Nil => Cons(y, Nil)
  case Cons(x, tail) => Cons(x, Snoc(tail,y))
}

lemma LengthSnoc<T>(xs : List<T>, x : T)
  ensures Length(Snoc(xs,x)) == Length(xs) + 1
{

}

function Append<T>(xs : List<T>, ys : List<T>) : List<T>
  ensures Length(Append(xs,ys)) == Length(xs) + Length(ys)
{
  match xs
  case Nil => ys
  case Cons(h, tail) => Cons(h, Append(tail, ys))
}

lemma {:induction false} SnocAppend<T>(xs : List<T>, y : T)
  ensures Snoc(xs, y) == Append(xs, Cons(y,Nil))
{
  match xs
  case Nil => {

  }
  case Cons(x,xtail) => {
    calc {
      Snoc(xs, y);
    ==
      Cons(x, Snoc(xtail,y));
    ==
      { SnocAppend(xtail, y); }
      Cons(x, Append(xtail, Cons(y,Nil)));
    ==
      Append(xs,Cons(y,Nil));
    }
  }
}


function ListToSeq<T>(l : List<T>) : seq<T>
{
  if l == Nil then []
  else [l.head] + ListToSeq(l.tail)
}

function SeqToList<T>(s : seq<T>) : List<T>
{
  if |s| == 0 then Nil else Cons(s[0],SeqToList(s[1..]))
}

lemma {:induction false} SeqToListReversible<T>(s : seq<T>)
  ensures ListToSeq(SeqToList(s)) == s
{
  if |s| == 0{

  }else{
    calc{
      ListToSeq(SeqToList(s));
    ==
      ListToSeq(Cons(s[0],SeqToList(s[1..])));
    ==
      [s[0]] + ListToSeq(SeqToList(s[1..]));
    ==
      { SeqToListReversible(s[1..]);}
      [s[0]] + s[1..];
    ==
     s;
    }
  }
}

lemma SeqSplit<T>(s: seq<T>, i: int)
  requires 0 <= i <= |s|
  ensures s == s[..i] + s[i..]
{
}

function rev<T>(s: seq<T>): seq<T>
{
  if |s| == 0 then []
  else rev(s[1..]) + [s[0]]
}

lemma ReverseConcat<T>(a: seq<T>, b: seq<T>)
  ensures rev(a + b) == rev(b) + rev(a)
{
  var c := a + b;
  if |a| == 0{
    calc{
      rev(a + b);
    ==
      {assert a + b == b;}
      rev(b);
    ==
      rev(b) + rev(a);
    }
  }else if |b| == 0{
    calc{
      rev(a + b);
    ==
      {assert a + b == a;}
      rev(a);
    ==
      rev(b) + rev(a);
    }
  }else{
    calc{
      rev(a + b);
    ==
      rev((a + b)[1..]) + [a[0]];
    ==
      { 
        assert (a + b)[1..] == a[1..] + b;
        ReverseConcat(a[1..],b);
      }
      rev(b) + rev(a[1..]) + [a[0]];
    ==
      rev(b) + rev(a);
    }
  }
}

lemma RevInvolution<T>(s : seq<T>)
  ensures rev(rev(s)) == s 
{
  if |s| == 0 {

  }else{
    calc{
      rev(rev(s));
    ==
      rev(rev(s[1..]) + [s[0]]);
    ==
      {ReverseConcat(rev(s[1..]), [s[0]]);}
      rev([s[0]]) + rev(rev(s[1..]));
    ==
      {RevInvolution((s[1..]));}
      rev([s[0]]) + s[1..];
    ==
      [s[0]] + s[1..];
    ==
      s;
    }
  }
}

function Take<T>(xs : List<T>, n : nat) : List<T>
  requires n <= Length(xs)
{
  if n == 0 then Nil else Cons(xs.head, Take(xs.tail,n - 1))
}

function Take1<T>(xs : List<T>, n : nat) : List<T>
{
  match xs
  case Nil => Nil
  case Cons(xhead, xtail) => 
    if n == 0 then Nil else Cons(xhead, Take1(xtail, n - 1))
}

function Drop<T>(xs : List<T>, n : nat) : List<T>
  requires n <= Length(xs) 
{
  if n == 0 then xs else Drop(xs.tail, n - 1)
}

function Drop1<T>(xs : List<T>, n : nat) : List<T> 
{
  match xs
  case Nil => Nil
  case Cons(_, xtail) =>
    if n == 0 then xs else Drop1(xtail, n - 1)
}

lemma TakeAndTake1SameRes<T>(xs : List<T>, n : nat)
  ensures (n <= Length(xs)) ==> Take(xs,n) == Take1(xs,n)
{

}

lemma DropAndDrop1SameRes<T>(xs : List<T>, n : nat)
  ensures (n <= Length(xs)) ==> Drop(xs,n) == Drop1(xs,n)
{
  
}

function At<T>(xs : List<T>, n : nat): T
  requires n < Length(xs)
{
  if n == 0 then xs.head else At(xs.tail, n - 1)
}

function ReverseSlow<T>(xs : List<T>) : List<T>
{
  if xs == Nil then Nil else Snoc(ReverseSlow(xs.tail), xs.head)
}

/*lemma ReverseInvolution<T>(xs : List<T>)
  ensures ReverseSlow(ReverseSlow(xs)) == xs
{
  match xs
  case Nil => {
  }
  case Cons(xhead, xtail) => {
    calc{
      ReverseSlow(ReverseSlow(xs));
    ==
      ReverseSlow(Snoc(ReverseSlow(xtail), xhead));
    ==
      {SnocAppend(ReverseSlow(xtail),xhead);}
      ReverseSlow(Append(ReverseSlow(xtail), Cons(xhead, Nil)));
    }
  }
}*/