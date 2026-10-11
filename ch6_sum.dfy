datatype List<T> = Nil | Cons(head: T, tail: List<T>)

//6.0
function Length<T>(xs: List<T>): nat {
  match xs
  case Nil => 0
  case Cons(_, tail) => 1 + Length(tail)
}

//6.0
function Length'<T>(xs : List<T>) : nat {
  if xs == Nil then 0 else 1 + Length'(xs.tail)
}

lemma {:induction false} lengthSame<T>(xs : List<T>)
  ensures Length'(xs) == Length(xs)
{
  if xs == Nil {

  }else{
    calc {
      Length'(xs);
    ==
      1 + Length'(xs.tail);
    ==
      {lengthSame(xs.tail);}
      {assert Length'(xs.tail) == Length(xs.tail);}
      1 + Length(xs.tail);
    ==
      Length(xs);
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
  if xs == Nil {

  }else{
    calc{
      Length(Snoc(xs, x));
    ==
      Length(Cons(xs.head, Snoc(xs.tail, x)));
    ==
      1 + Length(Snoc(xs.tail, x));
    ==
      { LengthSnoc(xs.tail, x); }
      { assert Length(Snoc(xs.tail, x)) == Length(xs.tail) + 1;}
      1 + 1 + Length(xs.tail);
    ==
      1 + Length(xs);
    }
  }
}

function Append<T>(xs: List<T>, ys: List<T>): List<T> {
  match xs
  case Nil => ys
  case Cons(x, tail) => Cons(x, Append(tail, ys))
}

lemma LengthAppend<T>(xs: List<T>, ys: List<T>)
  ensures Length(Append(xs, ys)) == Length(xs) + Length(ys)
{
}

//6.2
lemma {:induction false} SnocCaseOfAppend<T>(xs : List<T>, y: T)
  ensures Snoc(xs, y) == Append(xs, Cons(y,Nil))
{
  if xs == Nil{

  }else{
    var tail,x := xs.tail, xs.head;

    calc {
      Cons(x, Snoc(tail, y));
    ==
      {
        SnocCaseOfAppend(tail, y);
        assert Snoc(tail,y) == Append(tail, Cons(y, Nil));
      }
      Cons(x, Append(tail, Cons(y, Nil)));
    ==
      Append(xs, Cons(y, Nil));
    }
  }
}

//6.3
lemma {:induction false} AppendNil<T>(xs: List<T>)
  ensures Append(xs, Nil) == xs
{
  if xs == Nil{

  }else{
    var tail, x := xs.tail, xs.head;
    calc {
      Append(xs, Nil);
    ==
      Cons(x, Append(tail, Nil));
    ==
      {
        AppendNil(tail);
        assert Append(tail, Nil) == tail;
      }
      Cons(x, tail);
    ==
      xs;
    }
  }
}

//6.4
lemma {:induction false} AppendAssociative<T>(xs: List<T>, ys: List<T>, zs: List<T>)
  ensures Append(Append(xs, ys), zs) == Append(xs, Append(ys, zs))
{
  if xs == Nil {

  }else{
    var xtail, xhead := xs.tail, xs.head;
    calc{
      Append(xs, Append(ys, zs));
    ==
      Cons(xhead, Append(xtail, Append(ys, zs)));
    ==
      {
        AppendAssociative(xtail, ys, zs);
        assert Append(Append(xtail, ys), zs) == Append(xtail, Append(ys, zs));
      }
      Cons(xhead, Append(Append(xtail, ys), zs));
    ==
      Append(Cons(xhead, Append(xtail, ys)),zs);
    ==
      Append(Append(Cons(xhead, xtail), ys), zs);
    }
  }
}



