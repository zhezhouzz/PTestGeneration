let ax_list_mem_has_nth =
  "fun (l : 'c list) (v : 'c) ->\n\
  \  (list_mem l v) #==> (fun ((idx [@ex]) : int) ->\n\
  \  0 <= idx && idx < list_len l && list_nth_pred l idx v)"

let _p1 =
  "(Not(Forall(qv((ty(Ty_var a1))(x \
   v)))(body(Exists(qv((ty(Ty_constructor(unit())))(x \
   dummy_0)))(body(Exists(qv((ty(Ty_var a1))(x \
   x_0)))(body(Implies(Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_var \
   a1)(Ty_constructor(bool()))))(x p1))(((ty(Ty_var a1))(x(AVar((ty(Ty_var \
   a1))(x \
   v))))))))))(And((Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_constructor(unit()))(Ty_arrow(Ty_constructor(unit()))(Ty_constructor(bool())))))(x \
   ==))(((ty(Ty_constructor(unit())))(x(AVar((ty(Ty_constructor(unit())))(x \
   dummy_0)))))((ty(Ty_constructor(unit())))(x(AC \
   U))))))))(And((Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_var \
   a1)(Ty_constructor(bool()))))(x p1))(((ty(Ty_var a1))(x(AVar((ty(Ty_var \
   a1))(x \
   x_0))))))))))(Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_var \
   a1)(Ty_arrow(Ty_var a1)(Ty_constructor(bool())))))(x ==))(((ty(Ty_var \
   a1))(x(AVar((ty(Ty_var a1))(x v)))))((ty(Ty_var a1))(x(AVar((ty(Ty_var \
   a1))(x x_0))))))))))))))))))))))"

let _p2 =
  "(Not(Forall(qv((ty(Ty_var a))(x \
   v)))(body(Implies(Or((Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_var \
   a)(Ty_constructor(bool()))))(x p1))(((ty(Ty_var a))(x(AVar((ty(Ty_var a))(x \
   v))))))))))(Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_var \
   a)(Ty_constructor(bool()))))(x p2))(((ty(Ty_var a))(x(AVar((ty(Ty_var a))(x \
   v))))))))))))(Exists(qv((ty(Ty_constructor(bool())))(x \
   x)))(body(And((Lit((ty(Ty_constructor(bool())))(x(AC(B \
   true)))))(Or((And((Lit((ty(Ty_constructor(bool())))(x(AVar((ty(Ty_constructor(bool())))(x \
   x))))))(Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_var \
   a)(Ty_constructor(bool()))))(x p1))(((ty(Ty_var a))(x(AVar((ty(Ty_var a))(x \
   v))))))))))))(And((Not(Lit((ty(Ty_constructor(bool())))(x(AVar((ty(Ty_constructor(bool())))(x \
   x)))))))(Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_var \
   a)(Ty_constructor(bool()))))(x p2))(((ty(Ty_var a))(x(AVar((ty(Ty_var a))(x \
   v))))))))))))))))))))))"

let _p3 =
  "(Not(Forall(qv((ty(Ty_constructor(option((Ty_var a)))))(x \
   v)))(body(Implies(Exists(qv((ty(Ty_var a))(x \
   y)))(body(Or((Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_constructor(option((Ty_var \
   a_10))))(Ty_arrow(Ty_constructor(option((Ty_var \
   a_10))))(Ty_constructor(bool())))))(x \
   ==))(((ty(Ty_constructor(option((Ty_var \
   a_10)))))(x(AVar((ty(Ty_constructor(option((Ty_var a_10)))))(x \
   v)))))((ty(Ty_constructor(option((Ty_var \
   a_10)))))(x(AAppOp((ty(Ty_constructor(option((Ty_var a_10)))))(x \
   None))()))))))))(And((Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_constructor(option((Ty_var \
   a_11))))(Ty_arrow(Ty_constructor(option((Ty_var \
   a_11))))(Ty_constructor(bool())))))(x \
   ==))(((ty(Ty_constructor(option((Ty_var \
   a_11)))))(x(AVar((ty(Ty_constructor(option((Ty_var a_11)))))(x \
   v)))))((ty(Ty_constructor(option((Ty_var \
   a_11)))))(x(AAppOp((ty(Ty_arrow(Ty_var a_11)(Ty_constructor(option((Ty_var \
   a_11))))))(x Some))(((ty(Ty_var a_11))(x(AVar((ty(Ty_var a_11))(x \
   y))))))))))))))(Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_var \
   a)(Ty_constructor(bool()))))(x p1))(((ty(Ty_var a))(x(AVar((ty(Ty_var a))(x \
   y))))))))))))))))(Exists(qv((ty(Ty_constructor(int())))(x \
   x)))(body(And((And((Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_constructor(int()))(Ty_arrow(Ty_constructor(int()))(Ty_constructor(bool())))))(x \
   <=))(((ty(Ty_constructor(int())))(x(AC(I \
   0))))((ty(Ty_constructor(int())))(x(AC(I \
   10)))))))))(Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_constructor(int()))(Ty_arrow(Ty_constructor(int()))(Ty_constructor(bool())))))(x \
   <=))(((ty(Ty_constructor(int())))(x(AC(I \
   0))))((ty(Ty_constructor(int())))(x(AVar((ty(Ty_constructor(int())))(x \
   x))))))))))(Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_constructor(int()))(Ty_arrow(Ty_constructor(int()))(Ty_constructor(bool())))))(x \
   <=))(((ty(Ty_constructor(int())))(x(AVar((ty(Ty_constructor(int())))(x \
   x)))))((ty(Ty_constructor(int())))(x(AC(I \
   10)))))))))))(Exists(qv((ty(Ty_constructor(bool())))(x \
   x_27)))(body(And((Iff(Lit((ty(Ty_constructor(bool())))(x(AVar((ty(Ty_constructor(bool())))(x \
   x_27))))))(Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_constructor(int()))(Ty_arrow(Ty_constructor(int()))(Ty_constructor(bool())))))(x \
   <))(((ty(Ty_constructor(int())))(x(AVar((ty(Ty_constructor(int())))(x \
   x)))))((ty(Ty_constructor(int())))(x(AC(I \
   2))))))))))(Or((And((Lit((ty(Ty_constructor(bool())))(x(AVar((ty(Ty_constructor(bool())))(x \
   x_27))))))(Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_constructor(option((Ty_var \
   a))))(Ty_arrow(Ty_constructor(option((Ty_var \
   a))))(Ty_constructor(bool())))))(x ==))(((ty(Ty_constructor(option((Ty_var \
   a)))))(x(AVar((ty(Ty_constructor(option((Ty_var a)))))(x \
   v)))))((ty(Ty_constructor(option((Ty_var \
   a)))))(x(AAppOp((ty(Ty_constructor(option((Ty_var a)))))(x \
   None))()))))))))))(And((Not(Lit((ty(Ty_constructor(bool())))(x(AVar((ty(Ty_constructor(bool())))(x \
   x_27)))))))(Exists(qv((ty(Ty_var a))(x \
   x_28)))(body(And((Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_var \
   a)(Ty_constructor(bool()))))(x p1))(((ty(Ty_var a))(x(AVar((ty(Ty_var a))(x \
   x_28))))))))))(Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_constructor(option((Ty_var \
   a))))(Ty_arrow(Ty_constructor(option((Ty_var \
   a))))(Ty_constructor(bool())))))(x ==))(((ty(Ty_constructor(option((Ty_var \
   a)))))(x(AVar((ty(Ty_constructor(option((Ty_var a)))))(x \
   v)))))((ty(Ty_constructor(option((Ty_var \
   a)))))(x(AAppOp((ty(Ty_arrow(Ty_var a)(Ty_constructor(option((Ty_var \
   a))))))(x Some))(((ty(Ty_var a))(x(AVar((ty(Ty_var a))(x \
   x_28))))))))))))))))))))))))))))))))))"

let _p4 =
  "(Not(Forall(qv((ty(Ty_constructor(list((Ty_var a)))))(x \
   l)))(body(Implies(Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_constructor(list((Ty_var \
   a))))(Ty_constructor(bool()))))(x p1))(((ty(Ty_constructor(list((Ty_var \
   a)))))(x(AVar((ty(Ty_constructor(list((Ty_var a)))))(x \
   l))))))))))(Forall(qv((ty(Ty_var a))(x \
   v)))(body(Implies(Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_constructor(list((Ty_var \
   a))))(Ty_arrow(Ty_var a)(Ty_constructor(bool())))))(x \
   list_mem))(((ty(Ty_constructor(list((Ty_var \
   a)))))(x(AVar((ty(Ty_constructor(list((Ty_var a)))))(x l)))))((ty(Ty_var \
   a))(x(AVar((ty(Ty_var a))(x \
   v))))))))))(Exists(qv((ty(Ty_constructor(int())))(x \
   x_33)))(body(And((Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_constructor(int()))(Ty_arrow(Ty_constructor(int()))(Ty_constructor(bool())))))(x \
   ==))(((ty(Ty_constructor(int())))(x(AVar((ty(Ty_constructor(int())))(x \
   x_33)))))((ty(Ty_constructor(int())))(x(AAppOp((ty(Ty_arrow(Ty_constructor(list((Ty_var \
   a))))(Ty_constructor(int()))))(x \
   list_len))(((ty(Ty_constructor(list((Ty_var \
   a)))))(x(AVar((ty(Ty_constructor(list((Ty_var a)))))(x \
   l))))))))))))))(Exists(qv((ty(Ty_constructor(int())))(x \
   x_34)))(body(And((Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_constructor(int()))(Ty_arrow(Ty_constructor(int()))(Ty_constructor(bool())))))(x \
   ==))(((ty(Ty_constructor(int())))(x(AVar((ty(Ty_constructor(int())))(x \
   x_34)))))((ty(Ty_constructor(int())))(x(AAppOp((ty(Ty_arrow(Ty_constructor(int()))(Ty_arrow(Ty_constructor(int()))(Ty_constructor(int())))))(x \
   -))(((ty(Ty_constructor(int())))(x(AVar((ty(Ty_constructor(int())))(x \
   x_33)))))((ty(Ty_constructor(int())))(x(AC(I \
   1)))))))))))))(Exists(qv((ty(Ty_constructor(int())))(x \
   x_36)))(body(And((Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_constructor(int()))(Ty_arrow(Ty_constructor(int()))(Ty_constructor(bool())))))(x \
   <=))(((ty(Ty_constructor(int())))(x(AC(I \
   0))))((ty(Ty_constructor(int())))(x(AVar((ty(Ty_constructor(int())))(x \
   x_34))))))))))(Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_constructor(int()))(Ty_arrow(Ty_constructor(int()))(Ty_constructor(bool())))))(x \
   <=))(((ty(Ty_constructor(int())))(x(AC(I \
   0))))((ty(Ty_constructor(int())))(x(AVar((ty(Ty_constructor(int())))(x \
   x_36))))))))))(Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_constructor(int()))(Ty_arrow(Ty_constructor(int()))(Ty_constructor(bool())))))(x \
   <=))(((ty(Ty_constructor(int())))(x(AVar((ty(Ty_constructor(int())))(x \
   x_36)))))((ty(Ty_constructor(int())))(x(AVar((ty(Ty_constructor(int())))(x \
   x_34))))))))))(Exists(qv((ty(Ty_var a))(x \
   x_37)))(body(And((Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_constructor(int()))(Ty_arrow(Ty_constructor(int()))(Ty_constructor(bool())))))(x \
   <=))(((ty(Ty_constructor(int())))(x(AC(I \
   0))))((ty(Ty_constructor(int())))(x(AVar((ty(Ty_constructor(int())))(x \
   x_36))))))))))(Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_constructor(int()))(Ty_arrow(Ty_constructor(int()))(Ty_constructor(bool())))))(x \
   <))(((ty(Ty_constructor(int())))(x(AVar((ty(Ty_constructor(int())))(x \
   x_36)))))((ty(Ty_constructor(int())))(x(AAppOp((ty(Ty_arrow(Ty_constructor(list((Ty_var \
   a))))(Ty_constructor(int()))))(x \
   list_len))(((ty(Ty_constructor(list((Ty_var \
   a)))))(x(AVar((ty(Ty_constructor(list((Ty_var a)))))(x \
   l))))))))))))))(Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_constructor(list((Ty_var \
   a))))(Ty_arrow(Ty_constructor(int()))(Ty_arrow(Ty_var \
   a)(Ty_constructor(bool()))))))(x \
   list_nth_pred))(((ty(Ty_constructor(list((Ty_var \
   a)))))(x(AVar((ty(Ty_constructor(list((Ty_var a)))))(x \
   l)))))((ty(Ty_constructor(int())))(x(AVar((ty(Ty_constructor(int())))(x \
   x_36)))))((ty(Ty_var a))(x(AVar((ty(Ty_var a))(x \
   x_37))))))))))(Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_var \
   a)(Ty_arrow(Ty_var a)(Ty_constructor(bool())))))(x ==))(((ty(Ty_var \
   a))(x(AVar((ty(Ty_var a))(x v)))))((ty(Ty_var a))(x(AVar((ty(Ty_var a))(x \
   x_37)))))))))))))))))))))))))))))))))"

let _p5 =
  "(Not(Forall(qv((ty(Ty_constructor(int())))(x \
   a)))(body(Forall(qv((ty(Ty_constructor(int())))(x \
   b)))(body(Implies(Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_constructor(int()))(Ty_arrow(Ty_constructor(int()))(Ty_constructor(bool())))))(x \
   <=))(((ty(Ty_constructor(int())))(x(AVar((ty(Ty_constructor(int())))(x \
   a)))))((ty(Ty_constructor(int())))(x(AVar((ty(Ty_constructor(int())))(x \
   b))))))))))(Forall(qv((ty(Ty_constructor(int())))(x \
   v)))(body(Implies(And((Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_constructor(int()))(Ty_arrow(Ty_constructor(int()))(Ty_constructor(bool())))))(x \
   <=))(((ty(Ty_constructor(int())))(x(AVar((ty(Ty_constructor(int())))(x \
   a)))))((ty(Ty_constructor(int())))(x(AVar((ty(Ty_constructor(int())))(x \
   v))))))))))(Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_constructor(int()))(Ty_arrow(Ty_constructor(int()))(Ty_constructor(bool())))))(x \
   <=))(((ty(Ty_constructor(int())))(x(AVar((ty(Ty_constructor(int())))(x \
   v)))))((ty(Ty_constructor(int())))(x(AVar((ty(Ty_constructor(int())))(x \
   b))))))))))))(Exists(qv((ty(Ty_constructor(bool())))(x \
   x_11)))(body(And((Iff(Lit((ty(Ty_constructor(bool())))(x(AVar((ty(Ty_constructor(bool())))(x \
   x_11))))))(Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_constructor(int()))(Ty_arrow(Ty_constructor(int()))(Ty_constructor(bool())))))(x \
   <))(((ty(Ty_constructor(int())))(x(AVar((ty(Ty_constructor(int())))(x \
   b)))))((ty(Ty_constructor(int())))(x(AVar((ty(Ty_constructor(int())))(x \
   a)))))))))))(Not(Lit((ty(Ty_constructor(bool())))(x(AVar((ty(Ty_constructor(bool())))(x \
   x_11)))))))(Exists(qv((ty(Ty_constructor(int())))(x \
   x_14)))(body(And((Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_constructor(int()))(Ty_arrow(Ty_constructor(int()))(Ty_constructor(bool())))))(x \
   ==))(((ty(Ty_constructor(int())))(x(AVar((ty(Ty_constructor(int())))(x \
   x_14)))))((ty(Ty_constructor(int())))(x(AAppOp((ty(Ty_arrow(Ty_constructor(int()))(Ty_arrow(Ty_constructor(int()))(Ty_constructor(int())))))(x \
   -))(((ty(Ty_constructor(int())))(x(AVar((ty(Ty_constructor(int())))(x \
   b)))))((ty(Ty_constructor(int())))(x(AVar((ty(Ty_constructor(int())))(x \
   a))))))))))))))(Exists(qv((ty(Ty_constructor(int())))(x \
   x)))(body(And((And((Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_constructor(int()))(Ty_arrow(Ty_constructor(int()))(Ty_constructor(bool())))))(x \
   <=))(((ty(Ty_constructor(int())))(x(AC(I \
   0))))((ty(Ty_constructor(int())))(x(AVar((ty(Ty_constructor(int())))(x \
   x_14))))))))))(Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_constructor(int()))(Ty_arrow(Ty_constructor(int()))(Ty_constructor(bool())))))(x \
   <=))(((ty(Ty_constructor(int())))(x(AC(I \
   0))))((ty(Ty_constructor(int())))(x(AVar((ty(Ty_constructor(int())))(x \
   x))))))))))(Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_constructor(int()))(Ty_arrow(Ty_constructor(int()))(Ty_constructor(bool())))))(x \
   <=))(((ty(Ty_constructor(int())))(x(AVar((ty(Ty_constructor(int())))(x \
   x)))))((ty(Ty_constructor(int())))(x(AVar((ty(Ty_constructor(int())))(x \
   x_14))))))))))))(Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_constructor(int()))(Ty_arrow(Ty_constructor(int()))(Ty_constructor(bool())))))(x \
   ==))(((ty(Ty_constructor(int())))(x(AVar((ty(Ty_constructor(int())))(x \
   v)))))((ty(Ty_constructor(int())))(x(AAppOp((ty(Ty_arrow(Ty_constructor(int()))(Ty_arrow(Ty_constructor(int()))(Ty_constructor(int())))))(x \
   +))(((ty(Ty_constructor(int())))(x(AVar((ty(Ty_constructor(int())))(x \
   a)))))((ty(Ty_constructor(int())))(x(AVar((ty(Ty_constructor(int())))(x \
   x)))))))))))))))))))))))))))))))))))"

let _p6 =
  "(Not(Forall(qv((ty(Ty_tuple((Ty_var a)(Ty_var b))))(x \
   v)))(body(Implies(And((Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_var \
   a)(Ty_constructor(bool()))))(x p1))(((ty(Ty_var \
   a))(x(AProj((ty(Ty_tuple((Ty_var a)(Ty_var \
   b))))(x(AVar((ty(Ty_tuple((Ty_var a)(Ty_var b))))(x \
   v)))))0))))))))(Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_var \
   b)(Ty_constructor(bool()))))(x p2))(((ty(Ty_var \
   b))(x(AProj((ty(Ty_tuple((Ty_var a)(Ty_var \
   b))))(x(AVar((ty(Ty_tuple((Ty_var a)(Ty_var b))))(x \
   v)))))1))))))))))(Exists(qv((ty(Ty_var b))(x \
   x_21)))(body(And((Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_var \
   b)(Ty_constructor(bool()))))(x p2))(((ty(Ty_var b))(x(AVar((ty(Ty_var b))(x \
   x_21))))))))))(Exists(qv((ty(Ty_var a))(x \
   x_22)))(body(And((Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_var \
   a)(Ty_constructor(bool()))))(x p1))(((ty(Ty_var a))(x(AVar((ty(Ty_var a))(x \
   x_22))))))))))(Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_var \
   a)(Ty_arrow(Ty_var a)(Ty_constructor(bool())))))(x ==))(((ty(Ty_var \
   a))(x(AProj((ty(Ty_tuple((Ty_var a)(Ty_var \
   b))))(x(AVar((ty(Ty_tuple((Ty_var a)(Ty_var b))))(x v)))))0)))((ty(Ty_var \
   a))(x(AVar((ty(Ty_var a))(x \
   x_22))))))))))(Lit((ty(Ty_constructor(bool())))(x(AAppOp((ty(Ty_arrow(Ty_var \
   b)(Ty_arrow(Ty_var b)(Ty_constructor(bool())))))(x ==))(((ty(Ty_var \
   b))(x(AProj((ty(Ty_tuple((Ty_var a)(Ty_var \
   b))))(x(AVar((ty(Ty_tuple((Ty_var a)(Ty_var b))))(x v)))))1)))((ty(Ty_var \
   b))(x(AVar((ty(Ty_var b))(x x_21))))))))))))))))))))))"
