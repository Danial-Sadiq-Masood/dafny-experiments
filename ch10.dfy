method ex11_0_a(){
  var x := 0;

  while x != 100
    invariant true
  {
    x := x + 1;
  }
  
  assert x == 100;
}

method ex11_0_b(){
  var x := 20;

  while 10 < x
    invariant x % 2 == 0
    invariant x >= 10
  {
    x := x - 2;
  }
  
  assert x == 10;
}

method ex11_0_c(){
  var x := 20;

  while x < 20
    invariant x % 2 == 0
    invariant x >= 10
  {
    while true {

    }
  }
  
  assert x == 20;
}

/*method ex11_0_d(){
  var x := 3;

  while x < 2
    invariant x % 2 == 0
  {
  }
  
  assert x % 2 == 0;
}*/