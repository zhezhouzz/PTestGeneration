// Time is modeled as int

type tTime = int;

type tClockBoundTime = (earliest: tTime, latest: tTime);

// Request: ClockBound TimeNow
   event eGetClockBoundTimeNowReq: (requester: machine, requestId: int);

// Response: ClockBound TimeNow
   event eGetClockBoundTimeNowRsp: (requestId: int, now: tClockBoundTime);

// Request: Wait till wait_time has passed.
   event eWaitClockBoundTimeReq: (requester: machine, requestId: int, wait_time: tTime);

// Response: Wait till wait_time has passed.
   event eWaitClockBoundTimeRsp: (requestId: int);

// Event for P Spec, this event is triggered by internal open system
   event eMonitorGetClockBoundTimeNowRsp: (requestId: int, now: tClockBoundTime, ghost_trueTime: tTime, localClock: machine);

// There are three invarinats to guarantee based on eMonitorGetClockBoundTimeNowRsp

// prop diff_local_machine2 on eGetClockBoundTimeNowReq do {
//    var balanceMap: map[int, int];
//    var bank: machine;
// };

prop wf1 on eGetClockBoundTimeNowReq do e with
   self(e) == e.requester;

prop wf2 on eWaitClockBoundTimeReq do e with
   self(e) == e.requester;

prop requestId_incr1 on eGetClockBoundTimeNowReq do e with
   (forall (e1:eGetClockBoundTimeNowReq).e1.requestId < e.requestId) &&
   (forall (e2:eWaitClockBoundTimeReq).e2.requestId < e.requestId);

prop requestId_incr2 on eWaitClockBoundTimeReq do e with
   (forall (e1:eGetClockBoundTimeNowReq).e1.requestId < e.requestId) &&
   (forall (e2:eWaitClockBoundTimeReq).e2.requestId < e.requestId);

prop diff_local_machine on eGetClockBoundTimeNowReq do e with
   forall (e1:eGetClockBoundTimeNowReq).dest(e1) != dest(e);

prop no_adj_req on eGetClockBoundTimeNowReq do e with
   (forall (e1:eGetClockBoundTimeNowReq).not(last(e1))) &&
   (forall (e2:eWaitClockBoundTimeReq).not(last(e2)));

syn GeneratedClient on
   (eGetClockBoundTimeNowReq = (locolClocks, 3), eWaitClockBoundTimeReq = (locolClocks, 3)) with
   diff_local_machine, requestId_incr1,requestId_incr2, wf1, wf2, no_adj_req;
