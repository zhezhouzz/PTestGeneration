fun ( < ): forall 0. 0 -> 0 -> bool;

fun ( > ): forall 0. 0 -> 0 -> bool;

fun ( == ): forall 0. 0 -> 0 -> bool;

fun ( <= ): forall 0. 0 -> 0 -> bool;

fun ( >= ): forall 0. 0 -> 0 -> bool;

fun ( + ): int -> int -> int;

fun ( != ): forall 0. 0 -> 0 -> bool;

fun int_gen: machine -> int;
fun bool_gen: machine -> bool;
fun machine_gen: machine -> machine;

fun dest : forall 0. 0 -> machine;
fun last : forall 0. 0 -> bool;
fun self : forall 0. 0 -> machine;
fun choose : forall 0.forall 1. 0 -> 1;
