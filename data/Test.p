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

fun getGenerativeEvent(eventCounter: map[string, int]): (bool, string) {
   var choices: set[string];
   foreach ((k, v) in eventCounter)
   {
      if (v >= 0) {
         choices += (k);
      }
   }
   if (sizeof(choices) > 0) {
      return (true, k);
   } else {
      return (false, "");
   }
}
  
machine Client {
   var setting: setting;
   // history trace
   var reqSeq: seq[int];
   var rspSeq: seq[int]
   var trace: seq[string];
   // event counter
   var eventCounter: map[string, int];
   // temperal variable
   var nextEventName: string;


   
   start state Syn {
        entry (input: (setting: setting, domain_int: set[int], domain_bool: set[bool], domain_aid: set[int], domain_rid: set[int])) {
          setting = input.setting;
          domain_int = input.domain_int;
          domain_bool = input.domain_bool;
          domain_aid = input.domain_aid;
          domain_rid = input.domain_rid;
          counter = 0;
          domain_action += (Init);
          domain_action += (Withdraw);
          domain_action += (DoNothing);
          send_eInitAccount(this, setting, (accountId = 0, balance = 10));
          send_eWithDrawReq(this, setting, (rId = 0, accountId = 0, amount = choose(domain_int)));
        }

        on nextEvent do {
            var res: (bool, string);
            res = getGenerativeEvent(eventCounter);
            if (res.1) {
               nextEventName = res.2;
               goto genPayload;
            } else {
               goto slient;
            }
        }
    
        on syn_eWithDrawResp do {
          counter = counter + 1;
          if (counter < 2) {
              send_eWithDrawReq(this, setting, (rId = 0, accountId = 0, amount = choose(domain_int)));
          }
        }
   }

   state NextEvent do {
      entry{
         var res: (bool, string);
         res = getGenerativeEvent(eventCounter);
         if (res.1) {
            nextEventName = res.2;
         } else {
            raise halt;
         }
         // generate payload
         // check validate
         recordEvent(name, )
      }

      on Req do {
         
      }
   }

   state GenPayload do {
      entry{
         // fill by compiler
      }
   }

   state CheckValid do {
      entry{
         // fill by compiler
      }
   }

   state Send do {
      entry{
         // fill by compiler
      }
   }
}