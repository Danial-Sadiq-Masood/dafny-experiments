datatype Op = Add | Mul

datatype List<T> = Nil | Cons(head: T, tail: List<T>)

datatype Expr = Const(nat)
             | Var(string)
             | Node(op: Op, args: List<Expr>)
