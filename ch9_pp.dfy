module ListLibrary {
  // Ch. 6: Lists

  datatype List<T> = Nil | Cons(head: T, tail: List<T>)

  function Length<T>(xs: List<T>): int
    ensures Length(xs) >= 0
  {
    match xs
    case Nil => 0
    case Cons(_, tl) => 1 + Length(tl)
  }

  function Length'<T>(xs: List<T>): int
  {
    if xs.Nil? then 0 else  1 + Length(xs.tail)
  }

  // Ex 6.0
  lemma LengthIsLength'<T>(xs: List<T>)
    ensures Length(xs) == Length'(xs)
  {}

  function Snoc<T>(xs: List<T>, y: T): List<T>
  {
    match xs
    case Nil => Cons(y, Nil)
    case Cons(hd, tl) => Cons(hd, Snoc(tl, y))
  }

  // Ex 6.1
  lemma {:induction false} LengthSnoc<T>(xs: List<T>, y: T)
    ensures Length(Snoc(xs, y)) == Length(xs) + 1
  {
    match xs
    case Nil => {}
    case Cons(hd, tl) => {
      LengthSnoc(tl, y);
    }
  }

  function Append<T>(xs: List<T>, ys: List<T>): List<T>
    // intrinsic
    ensures Length(Append(xs, ys)) == Length(xs) + Length(ys)
  {
    match xs
    case Nil => ys
    case Cons(hd, tl) => Cons(hd, Append(tl, ys))
  }

  // extrinsic
  lemma LengthAppend<T>(xs: List<T>, ys: List<T>)
    ensures Length(Append(xs, ys)) == Length(xs) + Length(ys)
  {}

  // Ex 6.2
  lemma SnocIsAppend<T>(xs: List<T>, y: T)
    ensures Snoc(xs, y) == Append(xs, Cons(y, Nil))
  {}

  // Ex 6.3
  lemma {:induction false} AppendNil<T>(xs: List<T>)
    ensures Append(xs, Nil) == xs
  {
    match xs
    case Nil => {}
    case Cons(hd, tl) => { AppendNil(tl); }
  }

  // Ex 6.5
  lemma {:induction false} AppendDecomposition<T>(a: List<T>, b: List<T>, c: List<T>, d: List<T>)
    decreases a, c, b, d
    requires Length(a) == Length(c)
    requires Append(a, b) == Append(c, d)
    ensures a == c && b == d
  {
    match a
    case Nil => {}
    case Cons(ahd, atl) => { AppendDecomposition(a.tail, b, c.tail, d); }
  }

  lemma LengthNil<T>(xs: List<T>)
    ensures Length(xs) == 0 <==> xs.Nil?
  { }

  function SlowReverse<T>(xs: List<T>): List<T> {
    match xs
    case Nil => Nil
    case Cons(x, tail) => Snoc(SlowReverse(tail), x)
  }

  lemma LengthSlowReverse<T>(xs: List<T>)
    ensures Length(SlowReverse(xs)) == Length(xs){
    match xs
    case Nil =>
    case Cons(x, tail) =>
      LengthSnoc(SlowReverse(tail), x);
  }

  lemma SlowReverseNotNil<T>(xs : List<T>)
    requires xs != Nil
    ensures SlowReverse(xs) != Nil
  {

  }

  function ReverseAux<T>(xs: List<T>, acc: List<T>): List<T>
  {
    match xs
    case Nil => acc
    case Cons(x, tail) => ReverseAux(tail, Cons(x, acc))
  }

  lemma SnocAppend<T>(xs : List<T>, y : T)
    ensures Snoc(xs, y) == Append(xs, Cons(y, Nil)){

  }

  lemma AppendAssociative<T>(xs: List<T>, ys: List<T>, zs: List<T>)
    ensures Append(Append(xs, ys), zs) == Append(xs, Append(ys, zs))
  {
  }

  lemma ReverseAuxSlowCorrect<T>(xs: List<T>, acc: List<T>)
    ensures ReverseAux(xs, acc) == Append(SlowReverse(xs), acc){
    match xs
    case Nil =>
    case Cons(x, tail) =>
      calc {
        Append(SlowReverse(xs), acc);
      == // def. SlowReverse
        Append(Snoc(SlowReverse(tail), x), acc);
      ==
        { SnocAppend(SlowReverse(tail), x); }
        Append(Append(SlowReverse(tail), Cons(x, Nil)), acc);
      ==
        { AppendAssociative(SlowReverse(tail), Cons(x, Nil), acc); }
        Append(SlowReverse(tail), Append(Cons(x, Nil), acc));
      ==
        { assert Append(Cons(x, Nil), acc) == Cons(x, acc); }
        Append(SlowReverse(tail), Cons(x, acc));
      ==
        { ReverseAuxSlowCorrect(tail, Cons(x, acc)); }
        ReverseAux(tail, Cons(x, acc));
      ==
        // def. ReverseAux
        ReverseAux(xs, acc);
      }
  }

  function Reverse<T>(xs: List<T>): List<T> {
    //ReverseAux(xs, Nil)
    SlowReverse(xs)
  }

  lemma ReverseCorrect<T>(xs: List<T>)
    ensures Reverse(xs) == SlowReverse(xs)
  {
    
  }

  lemma ReverseAuxCorrect<T>(xs: List<T>, acc: List<T>)
    ensures ReverseAux(xs, acc) == Append(Reverse(xs), acc)
  {
    ReverseCorrect(xs);
    ReverseAuxSlowCorrect(xs, acc);
  }

  lemma LengthReverse<T>(xs: List<T>)
    ensures Length(Reverse(xs)) == Length(xs)
  {
    ReverseCorrect(xs);
    LengthSlowReverse(xs);
  }
}


module ImmutableQueue {
  import LL = ListLibrary

  datatype Queue<A> = FQ(front : LL.List<A>, back : LL.List<A>)
  function Empty(): Queue {
    FQ(LL.Nil, LL.Nil)
  }
  function Enqueue<A>(q: Queue, a: A): Queue {
    FQ(q.front, LL.Cons(a, q.back))
  }
  function Dequeue<A>(q: Queue): (A, Queue)
    requires q != Empty()
  {
    match q.front
    case Cons(x, frontTail) =>
      (x, FQ(frontTail, q.back))
    case Nil =>
      var front := LL.Reverse(q.back);
      (front.head, FQ(front.tail, LL.Nil))
  }

  ghost function Elements(q: Queue): LL.List {
    LL.Append(q.front, LL.Reverse(q.back))
  }

  lemma {:induction false} EmptyCorrect<A>()
    ensures Elements(Empty<A>()) == LL.Nil {

  }

  lemma EnqueueCorrect<A>(q: Queue, x: A)
    ensures Elements(Enqueue(q, x)) == LL.Snoc(Elements(q), x){
    match q
    case FQ(Nil, Nil) => {
      calc{
        Elements(Enqueue(q, x));
      ==
        Elements(FQ(q.front, LL.Cons(x, q.back)));
      ==
        Elements(FQ(LL.Nil, LL.Cons(x, LL.Nil)));
      ==
        LL.Append(LL.Nil, LL.Reverse(LL.Cons(x, LL.Nil)));
      ==
        LL.Reverse(LL.Cons(x, LL.Nil));
      ==
        LL.Snoc(LL.SlowReverse(LL.Nil), x);
      ==
        LL.Snoc(LL.Nil, x);
      ==
       LL.Snoc(Elements(q), x);
      }
    }
    case FQ(Cons(f,frontTail), Nil) => {
      calc {
        Elements(Enqueue(q, x));
      ==
        Elements(FQ(q.front, LL.Cons(x,LL.Nil)));
      ==
        LL.Append(q.front, LL.Reverse(LL.Cons(x,LL.Nil)));
      ==
        {
          assert LL.SlowReverse(LL.Cons(x,LL.Nil)) == LL.Snoc(LL.Nil, x);
        }
        LL.Append(q.front, LL.Cons(x, LL.Nil));
      ==
        {
          LL.AppendNil(q.front);
          assert q.front == LL.Append(q.front, LL.Nil);
        }
        LL.Append(LL.Append(q.front, LL.Nil), LL.Cons(x, LL.Nil));
      ==
        {
          assert LL.Append(q.front, LL.Nil) == LL.Append(q.front, q.back);
        }
        LL.Append(Elements(q), LL.Cons(x, LL.Nil));
      ==
        {
          LL.SnocAppend(Elements(q),x);
        }
        LL.Snoc(Elements(q), x);
      }
    }
    case FQ(Nil, back) => {
    
      calc{
        Elements(Enqueue(q, x));
      ==
        Elements(FQ(LL.Nil, LL.Cons(x,back)));
      ==
        LL.Append(LL.Nil, LL.Reverse(LL.Cons(x,back)));
      ==
        LL.Reverse(LL.Cons(x,back));
      ==
        LL.Snoc(LL.SlowReverse(back), x);
      ==
        LL.Snoc(LL.Reverse(back),x);
      ==
        LL.Snoc(LL.Append(LL.Nil,LL.Reverse(back)),x);
      ==
        LL.Snoc(Elements(FQ(LL.Nil, back)),x);
      ==
        LL.Snoc(Elements(q),x);
      }
    }
    case FQ(Cons(f,frontTail), Cons(b,backTail)) => {
      calc {
        Elements(Enqueue(q, x));
      ==
        Elements(FQ(q.front, LL.Cons(x, q.back)));
      ==
        LL.Append(q.front, LL.Reverse(LL.Cons(x,q.back)));
      ==
        LL.Append(q.front, LL.SlowReverse(LL.Cons(x,q.back)));
      ==
        LL.Append(q.front, LL.Snoc(LL.Reverse(q.back), x));
      ==
        {
          LL.SnocAppend(LL.Reverse(q.back),x);
        }
        LL.Append(q.front, LL.Append(LL.Reverse(q.back), LL.Cons(x, LL.Nil)));
      ==
        {
          LL.AppendAssociative(q.front, LL.Reverse(q.back), LL.Cons(x, LL.Nil));
        }
        LL.Append(LL.Append(q.front, LL.Reverse(q.back)), LL.Cons(x, LL.Nil));
      ==
        LL.Append(Elements(q), LL.Cons(x, LL.Nil));
      ==
        {
          LL.SnocAppend(Elements(q), x);
        }
        LL.Snoc(Elements(q), x);
      }
    }
  }

  /*lemma {:induction false} DequeueCorrect(q: Queue)
    requires q != Empty()
    ensures var (a, qt) := Dequeue(q);
            LL.Cons(a, Elements(qt)) == Elements(q)
  {

  }*/
}