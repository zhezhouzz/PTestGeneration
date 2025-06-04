machine Client {
  var actions: seq[string];
  var counterMap: map[string, int];
  var eGetClockBoundTimeNowReq_seq: seq[(int, (requestId: int, requester: machine))];
  var eGetClockBoundTimeNowRsp_seq: seq[(int, (now: (earliest: int, latest: int), requestId: int))];
  var eWaitClockBoundTimeReq_seq: seq[(int, (requestId: int, requester: machine, wait_time: int))];
  var eWaitClockBoundTimeRsp_seq: seq[(int, (requestId: int))];
  var eMonitorGetClockBoundTimeNowRsp_seq: seq[(int, (ghost_trueTime: int, localClock: machine, now: (earliest: int, latest: int), requestId: int))];
  start state Init {
    entry {
      actions += ("eGetClockBoundTimeNowReq");
      actions += ("eWaitClockBoundTimeReq");
      counterMap["eGetClockBoundTimeNowReq"] = 3;
      counterMap["eWaitClockBoundTimeReq"] = 3;
      goto Main;
    }
  }
  state Main {
    entry {
      send();
      goto Main;
    }
    on eGetClockBoundTimeNowRsp do (input: (now: (earliest: int, latest: int), requestId: int)) {
      record_eGetClockBoundTimeNowRsp_seq(input);
    }
    on eWaitClockBoundTimeRsp do (input: (requestId: int)) {
      record_eWaitClockBoundTimeRsp_seq(input);
    }
    on eMonitorGetClockBoundTimeNowRsp do (input: (ghost_trueTime: int, localClock: machine, now: (earliest: int, latest: int), requestId: int)) {
      record_eMonitorGetClockBoundTimeNowRsp_seq(input);
    }
  }
  fun machine_gen() {
    var i: int;
    i = choose(2);
    if ((i <= 0)) {
      return choose(locolClocks);
    }
    if ((i <= 1)) {
      return choose(locolClocks);
    }
    return self;
  }
  fun int_gen() {
    var i: int;
    i = choose(4);
    if ((i <= 0)) {
      return choose(10);
    }
    if ((i <= 1)) {
      return choose(100);
    }
    if ((i <= 2)) {
      return choose(1000);
    }
    if ((i <= 3)) {
      return choose(10000);
    }
    return 0;
  }
  fun diff_local_machine2 (dest: machine, e: (requestId: int, requester: machine)): bool {
    var res: bool;
    var e1_res: bool;
    var e1: (int, (requestId: int, requester: machine));
    res = true;
    foreach (e1 in eGetClockBoundTimeNowReq_seq) {
      e1_res = (e1.1.requester != e.requester);
      if (e1_res) {
      } else {
        res = false;
        break;
      }
    }
    return res;
  }
  fun requestId_incr (dest: machine, e: (requestId: int, requester: machine)): bool {
    var res: bool;
    var e1_res: bool;
    var e1: (int, (requestId: int, requester: machine));
    res = true;
    foreach (e1 in eGetClockBoundTimeNowReq_seq) {
      e1_res = (e1.1.requestId < e.requestId);
      if (e1_res) {
      } else {
        res = false;
        break;
      }
    }
    return res;
  }
  fun wf (dest: machine, e: (requestId: int, requester: machine)): bool {
    var res: bool;
    res = (dest == e.requester);
    return res;
  }
  fun get_seq_length() {
    return (size(eGetClockBoundTimeNowReq_seq) + (size(eGetClockBoundTimeNowRsp_seq) + (size(eWaitClockBoundTimeReq_seq) + (size(eWaitClockBoundTimeRsp_seq) + size(eMonitorGetClockBoundTimeNowRsp_seq)))));
  }
  fun record_eGetClockBoundTimeNowReq_seq (x: (requestId: int, requester: machine)) {
    eGetClockBoundTimeNowReq_seq = (0, (get_seq_length(), x));
  }
  fun record_eGetClockBoundTimeNowRsp_seq (x: (now: (earliest: int, latest: int), requestId: int)) {
    eGetClockBoundTimeNowRsp_seq = (0, (get_seq_length(), x));
  }
  fun record_eWaitClockBoundTimeReq_seq (x: (requestId: int, requester: machine, wait_time: int)) {
    eWaitClockBoundTimeReq_seq = (0, (get_seq_length(), x));
  }
  fun record_eWaitClockBoundTimeRsp_seq (x: (requestId: int)) {
    eWaitClockBoundTimeRsp_seq = (0, (get_seq_length(), x));
  }
  fun record_eMonitorGetClockBoundTimeNowRsp_seq (x: (ghost_trueTime: int, localClock: machine, now: (earliest: int, latest: int), requestId: int)) {
    eMonitorGetClockBoundTimeNowRsp_seq = (0, (get_seq_length(), x));
  }
  fun send() {
    var action: string;
    while (true) {
      action = choose(actions);
      if ((action == "eGetClockBoundTimeNowReq")) {
        if (send_eGetClockBoundTimeNowReq()) {
          break;
        }
      }
      if ((action == "eWaitClockBoundTimeReq")) {
        if (send_eWaitClockBoundTimeReq()) {
          break;
        }
      }
    }
  }
  fun send_eGetClockBoundTimeNowReq() {
    var dest: machine;
    var payload: (requestId: int, requester: machine);
    dest = choose(locolClocks);
    payload = (requestId = int_gen(), requester = machine_gen());
    if ((counterMap["eGetClockBoundTimeNowReq"] <= 0)) {
      return false;
    }
    if (wf(dest, payload)) {
    } else {
      return false;
    }
    if (diff_local_machine2(dest, payload)) {
    } else {
      return false;
    }
    if (requestId_incr(dest, payload)) {
    } else {
      return false;
    }
    record_eGetClockBoundTimeNowReq_seq(payload);
    counterMap["eGetClockBoundTimeNowReq"] = (counterMap["eGetClockBoundTimeNowReq"] - 1);
    send dest, eGetClockBoundTimeNowReq, payload;
    return true;
  }
  fun send_eWaitClockBoundTimeReq() {
    var dest: machine;
    var payload: (requestId: int, requester: machine, wait_time: int);
    dest = choose(locolClocks);
    payload = (requestId = int_gen(), requester = machine_gen(), wait_time = int_gen());
    if ((counterMap["eWaitClockBoundTimeReq"] <= 0)) {
      return false;
    }
    record_eWaitClockBoundTimeReq_seq(payload);
    counterMap["eWaitClockBoundTimeReq"] = (counterMap["eWaitClockBoundTimeReq"] - 1);
    send dest, eWaitClockBoundTimeReq, payload;
    return true;
  }
}


