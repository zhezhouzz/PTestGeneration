enum tTxnStatus {
                ERROR,
                ACTIVE,
                COMMITTED,
                ABORTED
                }

enum tCmdStatus {
                UNKNOWN,
                OK,
                ABORT
                }

type tGid = int;
type tKey = int;
type tVal = int;

type tStartTxnReq = (client: machine);
   event eStartTxnReq: tStartTxnReq;

type tStartTxnRsp = (router: machine, gid: tGid, start_time: tTime);
   event eStartTxnRsp: tStartTxnRsp;

type tReadReq = (gid: tGid, key: tKey);
   event eReadReq: tReadReq;

type tReadRsp = (router: machine, gid: tGid, key: tKey, val: tVal, status: tCmdStatus);
   event eReadRsp: tReadRsp;

type tUpdateReq = (gid: tGid, key: tKey, val: tVal);
   event eUpdateReq: tUpdateReq;

type tUpdateRsp = (router: machine, gid: tGid, key: tKey, val: tVal, status: tCmdStatus);
   event eUpdateRsp: tUpdateRsp;

type tCommitTxnReq = (gid: tGid);
   event eCommitTxnReq: tCommitTxnReq;

type tCommitTxnRsp = (gid: tGid, status: tTxnStatus);
   event eCommitTxnRsp: tCommitTxnRsp;

type tRollbackTxnReq = (gid: tGid);
   event eRollbackTxnReq: tRollbackTxnReq;

prop wf1 on eStartTxnReq do e with
   self(e) == e.client;

prop wf2 on eReadReq do e with
   (forall (e1:eCommitTxnRsp). e1.gid != e.gid) &&
   (forall (e2:eRollbackTxnReq). e2.gid != e.gid) &&
   (exists (e3:eStartTxnRsp). e3.gid == e.gid);

prop wf3 on eUpdateReq do e with
   (forall (e1:eCommitTxnRsp). e1.gid != e.gid) &&
   (forall (e2:eRollbackTxnReq). e2.gid != e.gid) &&
   (exists (e3:eStartTxnRsp). e3.gid == e.gid);

prop wf4 on eCommitTxnReq do e with
   (forall (e1:eCommitTxnRsp). e1.gid != e.gid) &&
   (forall (e2:eRollbackTxnReq). e2.gid != e.gid) &&
   (exists (e3:eStartTxnRsp). e3.gid == e.gid);

prop wf5 on eRollbackTxnReq do e with
   (forall (e1:eCommitTxnRsp). e1.gid != e.gid) &&
   (forall (e2:eRollbackTxnReq). e2.gid != e.gid) &&
   (exists (e3:eStartTxnRsp). e3.gid == e.gid);

prop write_same_key on eUpdateReq do e with
   (forall (e1:eUpdateReq). e1.gid == e.gid) &&
   (forall (e2:eReadReq). e2.gid == e.gid);

prop read_same_key on eReadReq do e with
   (forall (e1:eUpdateReq). e1.gid == e.gid) &&
   (forall (e2:eReadReq). e2.gid == e.gid);

prop read_after_two_write on eReadReq do e with
   exists (e1:eUpdateReq).exists (e2:eUpdateReq). e1.val != e2.val;

syn GeneratedClient on
   (eStartTxnReq = (coordinatorSet, 1),
    eReadReq = (coordinatorSet, 2),
    eUpdateReq = (coordinatorSet, 2),
    eCommitTxnReq = (coordinatorSet, 1)
    ) with
       wf1, wf2, wf3, wf4, wf5, write_same_key, read_same_key, read_after_two_write;
