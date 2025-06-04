type tTime = int;

type tClockBoundTime = (earliest: int, latest: int);

event req : (requestId: int, requester: machine);

event rsp : (now: (earliest: int, latest: int), requestId: int);

prop diff_local_machine =
   forall (e1:req).
   forall (e2:req).
   (e1 < e2) ==> (e1.requester != e2.requester);
