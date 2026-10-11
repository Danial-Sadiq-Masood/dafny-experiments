datatype Tree<T> = Leaf(data: T)
                | Node(left: Tree<T>, right: Tree<T>)

function Mirror<T>(t: Tree<T>): Tree<T> {
  match t
  case Leaf(_) => t
  case Node(left, right) => Node(Mirror(right), Mirror(left))
}

lemma {:induction false} MirrorMirror<T>(t: Tree<T>)
  ensures Mirror(Mirror(t)) == t
{
  match t
  case Leaf(_) => {
    assert Mirror(t) == t;
    calc {
      Mirror(Mirror(t));
    ==
      Mirror(t);
    ==
      t;
    }
  }
  case Node(left,right)=>{
    calc{
      Mirror(Mirror(Node(left,right)));
    ==
      Mirror(Node(Mirror(right), Mirror(left)));
    ==
      Node(Mirror(Mirror(left)), Mirror(Mirror(right)));
    ==
      {
        MirrorMirror(left);
        assert Mirror(Mirror(left)) == left;
        MirrorMirror(right);
        assert Mirror(Mirror(right)) == right;
      }
      Node(left, right);
    ==
      t;
    }
  }
}

function Size<T>(t: Tree<T>): nat {
  match t
  case Leaf(_) => 1
  case Node(left, right) => Size(left) + Size(right)
}

lemma {:induction false} MirrorSize<T>(t: Tree<T>)
  ensures Size(Mirror(t)) == Size(t)
{
  match t
  case Leaf(_) => {
    assert Size(Mirror(t)) == 1;
    assert Size(t) == 1;
    assert Size(t) == Size(Mirror(t));
  }
  case Node(left, right)=>{
    calc {
      Size(Mirror(t));
    ==
      Size(Node(Mirror(left), Mirror(right)));
    ==
      Size(Mirror(left)) + Size(Mirror(right));
    ==
      {
        MirrorSize(left);
        assert Size(Mirror(left)) == Size(left);
        MirrorSize(right);
        assert Size(Mirror(right)) == Size(right);
      }
      Size(left) + Size(right);
    ==
      Size(t);
    }
  }
}

