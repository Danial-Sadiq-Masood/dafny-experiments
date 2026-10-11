/*datatype BYTree = BlueLeaf | YellowLeaf | Node(left : BYTree, right : BYTree)

function ReverseColors(node : BYTree) : BYTree
  decreases node
{
  match node
  case BlueLeaf => YellowLeaf
  case YellowLeaf => BlueLeaf
  case Node(left, right) => Node(ReverseColors(left), ReverseColors(right))
}

function Oceanizee(node : BYTree) : BYTree
  decreases node
{
  match node
  case BlueLeaf => BlueLeaf
  case YellowLeaf => BlueLeaf
  case Node(left, right) => Node(ReverseColors(left), ReverseColors(right))
}

function LeftDepth(node : BYTree) : nat
{
  if node.BlueLeaf? then 0
  else if node.YellowLeaf? then 0
  else LeftDepth(node.left) + 1
}*/

/*datatype Color = Blue | Yellow | Green | Red

predicate IsSwedishFlagColor(c: Color) {
  c.Blue? || c.Yellow?
}

datatype ColoredTree = Leaf(Color)
                     | Node(ColoredTree, ColoredTree)

predicate IsSwedishFlagColorTree(node : ColoredTree)
{
  match node
  case Leaf(c) => IsSwedishFlagColor(c)
  case Node(left, right) => IsSwedishFlagColorTree(left) && IsSwedishFlagColorTree(right)
}
*/

/*
datatype Tree<T> = Leaf(data: T)
                 | Node(left: Tree<T>, right: Tree<T>)

function Mirror<T>(t : Tree<T>) : Tree<T>
{
  match t
  case Leaf(d) => Leaf(d)
  case Node(left, right) => Node(right, left) 
}

lemma MirrorInvolution<T>(t : Tree<T>)
  ensures Mirror(Mirror(t)) == t
{
}
*/

datatype Op = Add | Mul

datatype List<T> = Nil | Cons(head: T, tail: List<T>)

datatype Expr = Const(nat)
              | Var(string)
              | Node(op: Op, args: List<Expr>)

function Eval(e: Expr, env: map<string, nat>): nat {
  match e
  case Const(c) => c
  case Var(s) => if s in env.Keys then env[s] else 0
  case Node(op, args) => EvalList(op, args, env)
}

function EvalList(op: Op,args: List<Expr>, 
                  env: map<string, nat>): nat
  decreases args
{
  match args
  case Nil =>
    (match op case Add => 0 case Mul => 1)
  case Cons(e, tail) =>
    var v0, v1 := Eval(e, env), EvalList(op, tail, env);
    match op
    case Add => v0 + v1
    case Mul => v0 * v1
}


