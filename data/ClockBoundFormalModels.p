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

prop invaraint1 =
    forall (e1 e2: eMonitorGetClockBoundTimeNowRsp). (e1 < e2 && e1.localClock == e2.localClock) ==> (e1.now.earliest < e2.now.earliest);

prop invaraint2 =
    forall (e1 e2: eMonitorGetClockBoundTimeNowRsp). (e1 < e2) ==> (e1.now.earliest < e2.now.latest)

prop invaraint3 =
    forall (e1 e2: eMonitorGetClockBoundTimeNowRsp). (e1.now.latest < e2.now.earliest) ==> (e1 < e2)

// To target the first invaraint, we can only send request to one local machine

prop unique_local_machine =
    forall (e1 e2: eGetClockBoundTimeNowReq | eWaitClockBoundTimeReq).
        e1.localClock == e2.localClock;

// To target the second invaraint, we can also focus on consistency over different machines
prop invaraint2_diff =
    forall (e1 e2: eMonitorGetClockBoundTimeNowRsp). (e1 < e2 && e1.localClock != e2.localClock) ==> (e1.now.earliest < e2.now.latest)

// We can send to machine always different from the last monitor event
prop get_payload on (e: eGetClockBoundTimeNowReq) =
    exists em. 
        ((em: eMonitorGetClockBoundTimeNowRsp) && (forall (em': eMonitorGetClockBoundTimeNowRsp). em' < em)) ==> e.dest != em.localClock;

// We can force one local clock updaed for 3 times
prop three_times on (e: eGetClockBoundTimeNowReq) =
    exists (e1 e2 e3: eMonitorGetClockBoundTimeNowRsp). e1 < e2 && e2 < e3 && e1.localClock == e2.localClock && e2.localClock == e3.localClock;

// eWaitClockBoundTimeReq seems not quite useful
syn Client on [(eGetClockBoundTimeNowReq, 5), (eWaitClockBoundTimeReq, 3)] with [get_payload, three_times];