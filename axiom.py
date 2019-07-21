axiom_name = 'addition-commutativity'

_a : PEGNode
_b : PEGNode

lhs = _a + _b
rhs = _b + _a

###

axiom_name = 'addition-associativity-1'

_a : PEGNode
_b : PEGNode
_c : PEGNode

lhs = _a + (_b + _c)
rhs = _a + _b + _c

###

axiom_name = 'addition-associativity-2'

_a : PEGNode
_b : PEGNode
_c : PEGNode

lhs = (_a + _b) + _c
rhs = _a + (_b + _c)

###

axiom_name = 'addition-neutral'

_a : PEGNode

lhs = _a + 0
rhs = _a

###

axiom_name = 'addition-neutral2'

_a : PEGNode

lhs = 0 + _a
rhs = _a

###

axiom_name = 'multiply-by-zero'

_a : PEGNode
_a.expr_type = 'NumNode'

lhs = _a * 0
rhs = 0

###

axiom_name = 'addition-multiplication-distributivity-1'

_a: PEGNode
_b: PEGNode
_c: PEGNode


lhs = (_a + _b) * _c
rhs = _a * _c + _b * _c

###

axiom_name = 'addition-multiplication-distributivity-2'

_a: PEGNode
_b: PEGNode
_c: PEGNode

rhs = _c * (_a + _b)
lhs = _a * _c + _b * _c

###

axiom_name = 'branch-with-true-condition'

_phi : PHINode
_t : PEGNode
_f : PEGNode

lhs = _phi(True, _t, _f)
rhs = _t

###

axiom_name = 'branch-with-false-condition'

_phi : PHINode
_t : PEGNode
_f : PEGNode

lhs = _phi(False, _t, _f)
rhs = _f

###

axiom_name = 'branch-with-same-cases'

_phi :PHINode
_cond : PEGNode
_case : PEGNode

lhs = _phi(_cond, _case, _case)
rhs = _case

###

axiom_name = 'equal-reflexivity'

_a : PEGNode

lhs = _a is _a
rhs = True

###

axiom_name = 'negated-equal-reflexivity'

_a : PEGNode

lhs = _a is not _a
rhs = False

###

axiom_name = 'arr-is-not-none'

_arr : NPArrayNode

_arr.expr_type = 'NPArrayNode'

lhs = not (_arr is None)
rhs = False

###

axiom_name = 'multiplication-neutral'

_a : PEGNode

lhs = _a * 1
rhs = _a

###

axiom_name = 'subtraction-neutral'

_a : PEGNode

lhs = _a - 0
rhs = _a

###

axiom_name = 'conjunction-neutral'

_a : PEGNode

lhs = _a and True
rhs = _a

###

axiom_name = 'disjunction-neutral'

_a : PEGNode

lhs = _a or False
rhs = _a

###

axiom_name = 'phi-addition-distributivity'

phi1 : PHINode
phi2 : PHINode
_cond : PEGNode
_t : PEGNode
_f : PEGNode
_a : PEGNode

lhs = phi1(_cond, _t, _f) + _a
rhs = phi2(_cond, _t + _a, _f + _a)

###

axiom_name = 'phi-multiplication-distributivity'

phi1 : PHINode
phi2 : PHINode
_cond : PEGNode
_t : PEGNode
_f : PEGNode
_a : PEGNode

lhs = phi1(_cond, _t, _f) * _a
rhs = phi2(_cond, _t * _a, _f * _a)

###

axiom_name = 'iteration-equals-initial'

_theta : THETANode
_a : PEGNode

lhs = _theta(_a, _theta)
rhs = _a

###

axiom_name = 'loop-invariance'

_eval : EvalNode
_a : PEGNode
_b : PEGNode

lhs = _eval(_a, _b)
rhs = _a

condition_1 = invariant(_a, _eval)

###

axiom_name = 'non-changing-loop-value'

_theta : THETANode
_a : PEGNode

lhs = _theta(_a, _a)
rhs = _a

###

axiom_name = 'fst-pass-true-iteration'

_pass : PassNode
_theta : THETANode
_a : PEGNode

lhs = _pass(_theta(True, _a))
rhs = 0

###

axiom_name = 'theta-multiplication-distributivity'

theta1 : THETANode
theta2 : THETANode
_a : PEGNode
_b : PEGNode
_c : PEGNode

theta2.var_name = theta1.var_name
theta2.loop_depth = theta1.loop_depth

lhs = theta1(_a, _b) * _c
rhs = theta2(_a * _c, _b * _c)


###

axiom_name = 'pass-true'

_pass : PassNode

lhs = _pass(True)
rhs = 0

###

axiom_name = 'negate-true'

lhs = not True
rhs = False

###

axiom_name = 'negate-false'

lhs = not False
rhs = True

###

axiom_name = 'evalutating-iteration-zero'

_eval : EvalNode
_theta : THETANode
_a : PEGNode
_b : PEGNode

lhs = _eval(_theta(_a, _b), 0)
rhs = _a

###

axiom_name = 'numpy-addition-commutativity'

_a : PEGNode
_b : PEGNode

lhs = np.add(_a, _b)
rhs = np.add(_b, _a)

###

axiom_name = 'numpy-addition-neutral'

_a : PEGNode

lhs = np.add(_a, 0)
rhs = _a


###

axiom_name = 'zeros-unique-elements'

_shape : PEGNode

lhs = np.unique(np.zeros(_shape))
rhs = np.array(0)

###

axiom_name = 'ones-unique-elements'

_shape : PEGNode

lhs = np.unique(np.ones(_shape))
rhs = np.array(1)

###

axiom_name = 'full-unique-elements'

_shape : PEGNode
_elem : PEGNode

lhs = np.unique(np.full(_shape, _elem))
rhs = np.array(_elem)

###

axiom_name = 'np-array-equal-reflexivity'

_a : NumNode

lhs = np.array_equal(a, a)
rhs = True

###

axiom_name = 'multiplication-of-exponentials'

_a : PEGNode
_b : PEGNode

lhs = np.exp(_a) * np.exp(_b)
rhs = np.exp(_a + _b)

###

axiom_name = 'flipud-symmetry'

_a : PEGNode

lhs = np.flipud(np.flipud(_a))
rhs = _a

###

axiom_name = 'fliplr-symmetry'

_a : PEGNode

lhs = np.fliplr(np.fliplr(_a))
rhs = _a


###

axiom_name = 'constant_loop_bounds_addition'

_init : PEGNode
_up : PEGNode
_th1 : THETANode
_th2 : THETANode
_eval : EvalNode
_pass : PassNode

range_obj = range(_up)
iter_value = _th2(next(iter(range_obj)), next(_th2))

lhs = _eval(_th1(_init, _th1 + iter_value), _pass(not iter_value in range_obj))
rhs = _init + ((_up - 1) * _up) // 2

###

axiom_name = 'constant-step-loop-addition'

_init : PEGNode
_up : PEGNode
_th1 : THETANode
_th2 : THETANode
_eval : EvalNode
_p : PassNode
_val : PEGNode

_init.expr_type = 'NumNode'

range_obj = range(_up)
iter_value = _th2(next(iter(range_obj)), next(_th2))

lhs = _eval(_th1(_init, _th1 + _val), _p(not iter_value in range_obj))
rhs = _init + _up * _val

condition_1 = invariant(_val, _eval)


###

axiom_name = 'determinant-of-inverse'

_a : PEGNode

lhs = np.linalg.det(np.linalg.inv(_a))
rhs = 1 / np.linalg.det(_a)


###

axiom_name = 'matrix-2x2-trace'

_arr : NPArrayNode
_a11 : PEGNode
_a12 :PEGNode
_a21 : PEGNode
_a22 : PEGNode

_arr.shape = (2, 2)

matrix = _arr([[_a11, _a12],
                [_a21, _a22]])


lhs = np.trace(matrix)
rhs = _a11 + _a22


###

axiom_name = 'transform-vector-by-matrix-3d'

_mat : NPArrayNode
_a11 : PEGNode
_a12 : PEGNode
_a13 : PEGNode
_a21 : PEGNode
_a22 : PEGNode
_a23 : PEGNode
_a31 : PEGNode
_a32 : PEGNode
_a33 : PEGNode

_vec :NPArrayNode
_v1 : PEGNode
_v2 : PEGNode
_v3 : PEGNode

_mat.shape = (3, 3)
_vec.shape = (3,)

matrix = _mat([[_a11, _a12, _a13],
               [_a21, _a22, _a23],
               [_a31, _a32, _a33]])

vector = _vec([_v1, _v2, _v3])

lhs = np.dot(matrix, vector)
rhs = np.array([_a11 * _v1 + _a12 * _v2 + _a13 * _v3,
                _a21 * _v1 + _a22 * _v2 + _a23 * _v3,
                _a31 * _v1 + _a32 * _v2 + _a33 * _v3])

###

axiom_name = 'sin-of-sum'

_a : PEGNode
_b : PEGNode

lhs = np.sin(_a) * np.cos(_b) + np.cos(_a) * np.sin(_b)
rhs = np.sin(_a + _b)