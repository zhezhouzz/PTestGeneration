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
   forall (e1: eMonitorGetClockBoundTimeNowRsp).
   forall (e2: eMonitorGetClockBoundTimeNowRsp).
   ((e1 < e2) && (e1.localClock == e2.localClock)) ==> (e1.now.earliest < e2.now.earliest);

prop invaraint2 =
   forall (e1: eMonitorGetClockBoundTimeNowRsp).
   forall (e2: eMonitorGetClockBoundTimeNowRsp).
   (e1 < e2) ==> (e1.now.earliest < e2.now.latest);

prop invaraint3 =
   forall (e1: eMonitorGetClockBoundTimeNowRsp).
   forall (e2: eMonitorGetClockBoundTimeNowRsp).
   (e1.now.latest < e2.now.earliest) ==> (e1 < e2);

// To target the first invaraint, we can only send request to one local machine

prop unique_local_machine =
   forall (e1:eGetClockBoundTimeNowReq).
   forall (e2:eGetClockBoundTimeNowReq).
   e1.requester == e2.requester;

prop diff_local_machine =
   forall (e1:eGetClockBoundTimeNowReq).
   forall (e2:eGetClockBoundTimeNowReq).
   (e1 < e2) ==> (e1.requester != e2.requester);

prop diff_local_machine2 on eGetClockBoundTimeNowReq do e with
   forall (e1:eGetClockBoundTimeNowReq).e1.requester != e.requester;

prop unique_local_machine2 on eGetClockBoundTimeNowReq do e with
   forall (e1:eGetClockBoundTimeNowReq).e1.requester == e.requester;

prop requestId_incr on eGetClockBoundTimeNowReq do e with
   forall (e1:eGetClockBoundTimeNowReq).e1.requestId < e.requestId;   

prop requestId_incr_gen on eGetClockBoundTimeNowReq {
   var e1: eGetClockBoundTimeNowReq;
   if (forall (e2:eGetClockBoundTimeNowReq). e1.requestId >= e2.requestId) {
      return (requester = *, requestId = e1.requestId + assume (0 < v));
   }
}

prop requestId_init_gen on eGetClockBoundTimeNowReq {
   if (forall (e2:eGetClockBoundTimeNowReq). false) {
      return (requester = *, requestId = assume (0 <= v));
   }
}

event writeReq: (requestId: int, key: int, value: int);
event writeRsp: (requestId: int, key: int, value: int, status: bool);

prop write_same_key on writeReq do e with
   forall (e1:writeReq).e1.key == e.key;

prop write_fail_retry on writeReq do e with
   exists (e1:writeReq).
      (exists (e2:writeRsp).
       (e1 < e2) && (e1.requestId == e2.requestId) && e2.status) || ((e.key == e1.key) && (e.value == e1.value));

prop write_fail_retry_gen on writeReq {
   var e1: writeReq;
   if (forall (e2:writeRsp). (e1 < e2) && (e1.requestId == e2.requestId) ==> !e2.status) {
      return (key = e1.key, value = e1.value);
   }
}

event readReq: (requestId: int, key: int);
event readRsp: (requestId: int, key: int, value: int, status: bool);

prop read_after_two_write_request on readReq do e with
   exists (e1: writeReq). exists (e2: writeReq).
   e1.status && e2.status && e1.key == e2.key && e1.value != e2.value && e1.key == e.key;

prop read_after_two_write_request_gen on readReq {
   var e1: writeReq;
   var e2: writeReq;
   if (e1.status && e2.status && e1.key == e2.key && e1.value != e2.value) {
      return (key = e1.key,);
   } else {
      error;
   }
}

prop no_adjacent_read on readReq do e with
   exists (e1: readReq). forall (e2: writeReq). e2 < e1;

// To target the second invaraint, we can also focus on consistency over different machines

prop invaraint2_diff =
   forall (e1: eMonitorGetClockBoundTimeNowRsp).
   forall (e2: eMonitorGetClockBoundTimeNowRsp).
   ((e1 < e2) && (e1.localClock != e2.localClock)) ==> (e1.now.earliest < e2.now.latest);

// We can send to machine always different from the last monitor event

prop get_payload on eGetClockBoundTimeNowReq do e with
   (forall (e1: eMonitorGetClockBoundTimeNowRsp). false) ||
   (forall (e2: eMonitorGetClockBoundTimeNowRsp).
    (dest(e) == e2.localClock) ==>
    (exists (e3: eMonitorGetClockBoundTimeNowRsp). e2 < e3));

// We can force one local clock updaed for 3 times
prop three_times on eGetClockBoundTimeNowReq do e with
   exists (e1: eMonitorGetClockBoundTimeNowRsp).
   exists (e2: eMonitorGetClockBoundTimeNowRsp).
   exists (e3: eMonitorGetClockBoundTimeNowRsp).
   (e1 < e2) && (e2 < e3) && (e1.localClock == e2.localClock) && (e2.localClock == e3.localClock);

// eWaitClockBoundTimeReq seems not quite useful
syn Client on (eGetClockBoundTimeNowReq = 5, eWaitClockBoundTimeReq = 3) with get_payload, three_times;
