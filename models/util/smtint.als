module util/smtint

abstract sig SintRef { aqclass: SintRef }
abstract sig Sint {}

/*
 * A collection of utility functions for using Sintegers in Alloy.
 * Note that integer overflows are silently truncated to the current bitwidth
 * using the 2's complement arithmetic, unless the "forbid overfows" option is
 * turned on, in which case only models that don't have any overflows are 
 * analyzed. 
 */

fun add  [n1, n2: Sint] : Sint { this/plus[n1, n2] }
fun plus [n1, n2: Sint] : Sint { /*PLACEHOLDER: n1 fun/add n2 */ n1 }

fun sub   [n1, n2: Sint] : Sint { this/minus[n1, n2] }
fun minus [n1, n2: Sint] : Sint { /*PLACEHOLDER: n1 fun/sub n2 */ n1 }

fun mul [n1, n2: Sint] : Sint { /*PLACEHOLDER: n1 fun/mul n2*/ n1 }

/**
 * Performs the division with "round to zero" semantics, except the following 3 cases
 * 1) if a is 0, then it returns 0
 * 2) else if b is 0, then it returns 1 if a is negative and -1 if a is positive
 * 3) else if a is the smallest negative integer, and b is -1, then it returns a
 */
fun div [n1, n2: Sint] : Sint { /*PLACEHOLDER: n1 fun/div n2*/ n1 }

/** answer is defined to be the unique integer that satisfies "a = ((a/b)*b) + remainder" */
fun rem [n1, n2: Sint] : Sint { /*PLACEHOLDER: n1 fun/rem n2*/ n1 }

/** negate */
fun negate [n: Sint] : Sint { /*PLACEHOLDER: 0 fun/sub n*/ n }

/** equal to */
pred eq [n1, n2: Sint] { /*PLACEHOLDER: int[n1] = int[n2]*/ }

/** greater than */
pred gt [n1, n2: Sint] { /*PLACEHOLDER: n1 > n2 */ }

/** less then */
pred lt [n1, n2: Sint] { /*PLACEHOLDER: n1 < n2 */ }

/** greater than or equal */
pred gte [n1, n2: Sint] { /*PLACEHOLDER: n1 >= n2*/ }

/** less than or equal */
pred lte [n1, n2: Sint] { /*PLACEHOLDER: n1 <= n2*/ }

/** integer is zero */
pred zero [n: Sint] { /*PLACEHOLDER: n = 0*/ }

/** positive */
pred pos  [n: Sint] { /*PLACEHOLDER n > 0*/ }

/** negative */
pred neg  [n: Sint] { /*PLACEHOLDER: n < 0*/ }

/** non-positive */
pred nonpos [n: Sint] { /*PLACEHOLDER: n <= 0*/ }

/** non-negative */
pred nonneg [n: Sint] { /*PLACEHOLDER: n >= 0*/ }

