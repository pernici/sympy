from collections import defaultdict
from sympy.combinatorics.perm_groups import PermutationGroup
from sympy.combinatorics.permutations import Permutation, _af_new, _af_invert
from sympy.core import Basic, Symbol, sympify, Add, Mul, S, Rational
from sympy.combinatorics.tensor_can import get_symmetric_group_sgs, bsgs_direct_product, canonicalize, canonical_free, riemann_bsgs

from functools import wraps

from sympy.core import S, Symbol, sympify, Tuple, Integer, Basic
from sympy.core.decorators import call_highest_priority
from sympy.core.sympify import SympifyError
from sympy.matrices import ShapeError
from sympy.simplify import simplify
from sympy import cacheit

class TensorIndexType(object):
    def __init__(self, name, metric_sym=0, dummy_fmt=None):
        """
        name   name of the tensor type

        metric_sym:
        0      symmetric
        1      antisymmetric
        None   no symmetry

        dummy_fmt name of the head of dummy indices; by default it is
        the name of the tensor type

        Examples
        ========

        >>> from sympy.tensor.tensor import TensorIndexType
        >>> Lorentz = TensorIndexType('Lorentz', dummy_fmt='L')
        """
        self.name = name
        self.metric_sym = metric_sym
        if not dummy_fmt:
            self.dummy_fmt = '%s_%%d' % self.name
        else:
            self.dummy_fmt = '%s_%%d' % dummy_fmt

    def __str__(self):
        return self.name

    __repr__ = __str__

class TensorIndex(object):
    """
    Tensor indices are contructed with the Einstein summation convention.

    An index can be in contravariant or in covariant form; in the latter
    case it is represented prepending a `-` to the index name.

    Dummy indices have the head given by `dummy_fmt`


    Examples
    ========

    >>> from sympy.tensor.tensor import TensorIndexType, TensorIndex, TensorSymmetry, TensorType, get_symmetric_group_sgs
    >>> Lorentz = TensorIndexType('Lorentz', dummy_fmt='L')
    >>> i = TensorIndex('i', Lorentz); i
    i
    >>> sym1 = TensorSymmetry(get_symmetric_group_sgs(1))
    >>> S1 = TensorType([Lorentz], sym1)
    >>> A, B = S1('A,B')
    >>> A(i)*B(-i)
    A(L_0)*B(-L_0)
    """
    def __init__(self, name, tensortype, is_contravariant=True):
        self.name = name
        self.tensortype = tensortype
        self.is_contravariant = is_contravariant

    def __str__(self):
        s = self.name
        if not self.is_contravariant:
            s = '-%s' % s
        return s

    __repr__ = __str__

    @cacheit
    def covariant(self):
        if self.is_contravariant:
            return TensorIndex(self.name, self.tensortype, False)
        else:
            return self

    def __eq__(self, other):
        return self.name == other.name and \
               self.tensortype == other.tensortype and \
               self.is_contravariant == other.is_contravariant

    __neg__ = covariant

def tensor_indices(s, typ):
    """
    Returns tensor indices given their name

    Examples
    ========

    >>> from sympy.tensor.tensor import TensorIndexType, tensor_indices
    >>> Lorentz = TensorIndexType('Lorentz', dummy_fmt='L')
    >>> a, b, c, d = tensor_indices('a,b,c,d', Lorentz)
    """
    a = s.split(',')
    return [TensorIndex(i, typ) for i in a]


class TensorSymmetry(object):
    """
    Symmetry of a tensor

    bsgs tuple (base, sgs) BSBS of the symmetry of the tensor

    Examples
    ========

    Examples
    ========

    Define a symmetric tensor
    >>> from sympy.tensor.tensor import TensorIndexType, tensor_indices, TensorSymmetry, TensorType, get_symmetric_group_sgs
    >>> Lorentz = TensorIndexType('Lorentz', dummy_fmt='L')
    >>> a, b, c, d = tensor_indices('a,b,c,d', Lorentz)
    >>> sym2 = TensorSymmetry(get_symmetric_group_sgs(2))
    >>> S2 = TensorType([Lorentz]*2, sym2)
    >>> V = S2('V')
    """
    def __init__(self, bsgs):
        self.base, self.generators = bsgs
        self.rank = self.generators[0].size

def _get_index_types(indices):
    res = []
    for i in indices:
        if isinstance(i, TensorIndex):
            res.append(i.tensortype)
        elif isinstance(i, TensorIndexType):
            res.append(i)
        else:
            raise NotImplementedError
    return res

def has_tensor(p):
    if p.is_Tensor:
        return True
    if p.is_Mul or p.is_Add:
        for x in p.args:
            if has_tensor(x):
                return True
    return False


class TensorType(Basic):
    """

    Examples
    ========

    Define a symmetric tensor
    >>> from sympy.tensor.tensor import TensorIndexType, tensor_indices, TensorSymmetry, TensorType, get_symmetric_group_sgs
    >>> Lorentz = TensorIndexType('Lorentz', dummy_fmt='L')
    >>> a, b, c, d = tensor_indices('a,b,c,d', Lorentz)
    >>> sym2 = TensorSymmetry(get_symmetric_group_sgs(2))
    >>> S2 = TensorType([Lorentz]*2, sym2)
    >>> V = S2('V')
    """
    is_commutative = False

    def __new__(cls, indices, symmetry, **kw_args):
        obj = Basic.__new__(cls, **kw_args)
        obj.index_types = []
        obj.index_types = _get_index_types(indices)
        obj.types = list(set(obj.index_types))
        obj.types.sort(key=lambda x: x.name)
        obj.symmetry = symmetry
        assert symmetry.rank == len(indices) + 2
        return obj

    def __str__(self):
        return 'TensorType(%s)' %([str(x) for x in self.index_types])

    def __call__(self, s, commuting=0):
        """
        commuting:
        None no commutation rule
        0    commutes
        1    anticommutes

        Examples
        ========

        Define symmetric tensors `V`, `W` and `G`, respectively commuting,
        anticommuting and with no commutation symmetry
        >>> from sympy.tensor.tensor import TensorIndexType, tensor_indices, TensorSymmetry, TensorType, get_symmetric_group_sgs, canon_bp
        >>> Lorentz = TensorIndexType('Lorentz', dummy_fmt='L')
        >>> a, b = tensor_indices('a,b', Lorentz)
        >>> sym2 = TensorSymmetry(get_symmetric_group_sgs(2))
        >>> S2 = TensorType([Lorentz]*2, sym2)
        >>> V = S2('V')
        >>> W = S2('W', 1)
        >>> G = S2('G', None)
        >>> canon_bp(V(a, b)*V(-b, -a))
        V(L_0, L_1)*V(-L_0, -L_1)
        >>> canon_bp(W(a, b)*W(-b, -a))
        0
        """
        names = s.split(',')
        if len(names) == 1:
            return TensorHead(names[0], self, commuting)
        else:
            return [TensorHead(name, self, commuting) for name in names]

class TensorHead(Basic):
    is_commutative = False

    def __new__(cls, name, typ, commuting, **kw_args):
        """
        tensor with given name, index types, symmetry, commutation rule

        Examples
        ========

        >>> from sympy.tensor.tensor import TensorIndexType, tensor_indices, TensorSymmetry, TensorType, get_symmetric_group_sgs
        >>> Lorentz = TensorIndexType('Lorentz', dummy_fmt='L')
        >>> a, b = tensor_indices('a,b', Lorentz)
        >>> sym2 = TensorSymmetry(get_symmetric_group_sgs(2))
        >>> S2 = TensorType([Lorentz]*2, sym2)
        >>> A = S2('A')
        """
        assert isinstance(name, basestring)

        obj = Basic.__new__(cls, **kw_args)
        obj.name = name
        obj.index_types = typ.index_types
        obj.rank = len(obj.index_types)
        obj.types = typ.types
        obj.symmetry = typ.symmetry
        obj.commuting = commuting
        return obj

    def __eq__(self, other):
        if not isinstance(other, TensorHead):
            return False
        return self.name == other.name and self.index_types == other.index_types

    def __neq__(self, other):
        return not self == other

    def commutes_with(self, other):
        """
        Returns 0 (1) if self and other (anti)commute
        Returns None if self and other do not (anti)commute
        """
        if self.commuting == None or other.commuting == None:
            return None
        return self.commuting * other.commuting


    def __str__(self):
        return '%s(%s)' %(self.name, ','.join([str(x) for x in self.index_types]))
    __repr__ = __str__

    def __call__(self, *indices):
        """
        tensor with indices

        Examples
        ========

        >>> from sympy.tensor.tensor import TensorIndexType, tensor_indices, TensorSymmetry, TensorType, get_symmetric_group_sgs
        >>> Lorentz = TensorIndexType('Lorentz', dummy_fmt='L')
        >>> a, b = tensor_indices('a,b', Lorentz)
        >>> sym2 = TensorSymmetry(get_symmetric_group_sgs(2))
        >>> S2 = TensorType([Lorentz]*2, sym2)
        >>> A = S2('A')
        >>> t = A(a, -b)
        """
        assert self.rank == len(indices)
        components = [self]
        free, dum =  Tensor.from_indices(indices, self.types)
        free.sort(key=lambda x: x[0].name)
        dum.sort()
        return Tensor(S.One, components, free, dum)


class TensExpr(Basic):
    """
    A tensor expression is an expression formed by tensors;
    currently the sums of tensors are distributed.

    A TensExpr can be a TensAdd or a Tensor.

    TensAdd objects are put in canonic form using the Butler-Portugal
    algorithm for canonicalization under monoterm symmetries.

    Tensor objects are formed by products of component tensors,
    and include a coefficient, which is a SymPy expression.
    """

    _op_priority = 11.0
    is_Tensor = True
    is_TensExpr = True
    is_TensMul = False
    is_TensAdd = False
    is_commutative = False

    def __neg__(self):
        return (-1)*self

    def __abs__(self):
        raise NotImplementedError

    #@call_highest_priority('__radd__')
    def __add__(self, other):
        if self.is_TensAdd:
            args = self.args + (other,)
            return TensAdd(*args)
        if other.is_TensAdd:
            args = (self,) + other.args
        return TensAdd(self, other)

    #@call_highest_priority('__add__')
    def __radd__(self, other):
        return TensAdd(other, self)

    #@call_highest_priority('__rsub__')
    def __sub__(self, other):
        return TensAdd(self, -other)

    #@call_highest_priority('__sub__')
    def __rsub__(self, other):
        return TensAdd(other, -self)

    #@call_highest_priority('__rmul__')
    def __mul__(self, other):
        #return TensMul(self, other)
        if self.is_TensAdd:
            return TensAdd(*[x*other for x in self.args])
        if other.is_TensAdd:
            return TensAdd(*[self*x for x in other.args])
        return Tensor.__mul__(self, other)

    #@call_highest_priority('__mul__')
    def __rmul__(self, other):
        if self.is_TensMul:
            coeff = other*self.coeff
            return Tensor(coeff, self.components, self.free, self.dum)
        return TensAdd(*[x*other for x in self.args])

    #@call_highest_priority('__rpow__')
    def __pow__(self, other):
        raise NotImplementedError

    #@call_highest_priority('__pow__')
    def __rpow__(self, other):
        raise NotImplementedError

    #@call_highest_priority('__rdiv__')
    def __div__(self, other):
        other = sympify(other)
        if other.is_Tensor:
            raise ValueError('cannot divide by a tensor')
        coeff = self.coeff/other
        return Tensor(coeff, self.components, self.free, self.dum, is_canon_bp=self._is_canon_bp)


    #@call_highest_priority('__div__')
    def __rdiv__(self, other):
        raise NotImplementedError()

    __truediv__ = __div__
    __rtruediv__ = __rdiv__

    def substitute_indices(self, *index_tuples):
        """
        Return a tensor with indices substituted according to `index_tuples`

        Examples
        ========

        from sympy.tensor.tensor import TensorIndexType, tensor_indices, TensorSymmetry, TensorType
        >>> from sympy.tensor.tensor import TensorIndexType, tensor_indices, TensorSymmetry, TensorType, get_symmetric_group_sgs
        >>> Lorentz = TensorIndexType('Lorentz', dummy_fmt='L')
        >>> i, j, k, l = tensor_indices('i,j,k,l', Lorentz)
        >>> sym2 = TensorSymmetry(get_symmetric_group_sgs(2))
        >>> S2 = TensorType([Lorentz]*2, sym2)
        >>> A, B = S2('A,B')
        >>> t = A(i, k)*B(-k, -j); t
        A(i, L_0)*B(-L_0, -j)
        >>> t.substitute_indices((i,j), (j, k))
        A(j, L_0)*B(-L_0, -k)
        """
        if self.is_TensMul:
            free = self.free
            free1 = []
            for i, v in index_tuples:
                for j, ipos, cpos in free:
                    if i.name == j.name and i.tensortype == j.tensortype:
                        if i.is_contravariant == j.is_contravariant:
                            free1.append((v, ipos, cpos))
                        else:
                            # replace i with an index with the same covariance of i
                            if j.is_contravariant:
                                ind = TensorIndex(v.name, v.tensortype)
                                free1.append((ind, ipos, cpos))
                            else:
                                ind = TensorIndex(v.name, v.tensortype)
                                ind = -ind
                                free1.append((ind, ipos, cpos))
            return Tensor(self.coeff, self.components, free1, self.dum)
        if self.is_TensAdd:
            args = self.args
            args1 = []
            for x in args:
                y = x.substitute_indices(*indices)
                args1.append(y)
            return TensAdd(args1)

class TensAdd(TensExpr):
    is_Tensor = True
    is_TensAdd = True

    def __new__(cls, *args, **kw_args):
        """
        args  tuple of addends
        """
        args = [sympify(x) for x in args if x]
        if not all(x.is_Tensor for x in args):
            raise ValueError('all arguments should be tensors')
        a = []
        for x in args:
            if x.is_TensAdd:
                a.extend(list(x.args))
            else:
                a.append(x)
        args = a
        indices = set([x[0] for x in args[0].free])
        if not all(set([y[0] for y in x.free]) == indices for x in args[1:]):
            raise ValueError('all tensors must have the same indices')
        obj = Basic.__new__(cls, **kw_args)
        args.sort(key=lambda x: (x.components, x.free, x.dum))
        a = []
        pprev = None
        prev = args[0]
        prev_coeff = prev.coeff
        changed = False
        new = 0
        for x in args[1:]:
            # if x and prev have the same tensor, update the coeff of prev
            if x.components == prev.components \
                    and x.free == prev.free and x.dum == prev.dum:
                prev_coeff = prev_coeff + x.coeff
                changed = True
                op = 0
            else:
                # x and prev are different; if not changed, prev has not
                # been updated; store it
                if not changed:
                    a.append(prev)
                else:
                    # get a tensor from prev with coeff=prev_coeff and store it
                    if prev_coeff:
                        t = Tensor(prev_coeff, prev.components,
                            prev.free, prev.dum)
                        a.append(t)
                # move x to prev
                op = 1
                pprev, prev = prev, x
                pprev_coeff, prev_coeff = prev_coeff, x.coeff
                changed = False
        # if the case op=0 prev was not stored; store it now
        # in the case op=1 x was not stored; store it now (as prev)
        if op == 0 and prev_coeff:
            prev = Tensor(prev_coeff, prev.components, prev.free, prev.dum)
            a.append(prev)
        elif op == 1:
            a.append(prev)
        if not a:
            return S.Zero

        # TODO introduce option not to use canon_bp automatically in TensAdd
        if all(x.is_TensMul for x in a):
            a = [x.canon_bp() for x in a]
        obj._args = tuple(a)
        obj.set_indices = indices
        return obj

    def canon_bp(self):
        args = [x.canon_bp() for x in self.args]
        args.sort(key=lambda x: (x.components, x.free, x.dum))
        return TensAdd(*args)

    def __eq__(self, other):
        return self - other == 0

    def _pretty(self):
        a = []
        #args = sorted(self.args)
        args = self.args
        for x in args:
            a.append(str(x))

        a.sort()
        s = ' + '.join(a)
        s = s.replace('+ -', '- ')
        return s

class Tensor(TensExpr):
    is_Tensor = True
    is_TensMul = True

    def __new__(cls, coeff, *args, **kw_args):
        """

        coeff SymPy expression coefficient of the tensor.

        args[0]   list of TensorHead of the component tensors.

        args[1]   list of (ind, ipos, icomp)
        where `ind` is a free index, `ipos` is the slot position
        of `ind` in the `icomp`-th component tensor.

        args[2] list of tuples representing dummy indices.
        (ipos1, ipos2, icomp1, icomp2) indicates that the contravariant
        dummy index is the `ipos1` slot position in the `icomp1`-th
        component tensor; the corresponding covariant index is
        in the `ipos2` slot position in the `icomp2`-th component tensor.
        """
        # composite tensor
        # p_i*p_i
        # t = Tensor(None, t1, t2)
        obj = Basic.__new__(cls)
        obj.components = args[0]
        obj.types = []
        for t in obj.components:
            obj.types.extend(t.types)
        obj.free = args[1]
        obj.dum = args[2]
        obj.rank = len(obj.free) + 2*len(obj.dum)
        obj.coeff = coeff
        obj._is_canon_bp = kw_args.get('is_canon_bp', False)

        return obj

    def __eq__(self, other):
        if not other.is_Tensor :
            return False
        res = self.components == other.components and \
            self.free == other.free and \
            self.dum == other.dum and self.coeff == other.coeff
        return res

    def __neq__(self, other):
        return not self == other

    @staticmethod
    def from_indices(indices, types):
        """
        Returns free, dum for single component tensor

        free         list of tuples (index, pos, 0),
                     where `pos` is the position of index in
                     the list of indices formed by the component tensors

        dum          list of tuples (pos_contr, pos_cov, 0, 0)


        """
        n = len(indices)
        if n == 1:
            return [(indices[0], 0, 0)], []

        # find the positions of the free indices and of the dummy indices
        free = [True]*len(indices)
        index_dict = {}
        dum = []
        for i, index in enumerate(indices):
            name = index.name
            typ = index.tensortype
            contr = index.is_contravariant
            if (name, typ) in index_dict:
                # found a pair of dummy indices
                is_contr, pos = index_dict[(name, typ)]
                # check consistency and update free
                if is_contr:
                    if contr:
                        raise ValueError('two equal contravariant indices in slots %d and %d' %(pos, i))
                    else:
                        free[pos] = False
                        free[i] = False
                else:
                    if contr:
                        free[pos] = False
                        free[i] = False
                    else:
                        raise ValueError('two equal covariant indices in slots %d and %d' %(pos, i))
                if contr:
                    dum.append((i, pos, 0, 0))
                else:
                    dum.append((pos, i, 0, 0))
            else:
                index_dict[(name, typ)] = index.is_contravariant, i

        free_indices = [(index, i, 0) for i, index in enumerate(indices) if free[i]]
        free = sorted(free_indices, key=lambda x: (x[0].tensortype, x[0].name))

        return free, dum

    def get_indices(self):
        """
        Returns the list of indices of the tensor

        The indices are listed in the order in which they appear in the
        component tensors.
        """
        indices = [None]*self.rank
        start = 0
        pos = 0
        vpos = []
        components = self.components
        for t in self.components:
            vpos.append(pos)
            pos += t.rank
        cdt = defaultdict(int)
        for indx, ipos, cpos in self.free:
            start = vpos[cpos]
            indices[start + ipos] = indx
        for ipos1, ipos2, cpos1, cpos2 in self.dum:
            start1 = vpos[cpos1]
            start2 = vpos[cpos2]
            typ1 = components[cpos1].index_types[ipos1]
            assert typ1 == components[cpos2].index_types[ipos2]
            fmt = typ1.dummy_fmt
            nd = cdt[typ1]
            indices[start1 + ipos1] = TensorIndex(fmt % nd, typ1)
            indices[start2 + ipos2] = TensorIndex(fmt % nd, typ1, False)
            cdt[typ1] += 1
        return indices

    def split(self):
        """
        Returns a list of tensors, whose proouct is `self`

        Dummy indices contracted among different tensor components
        become free indices with the same name as the one used to
        represent the dummy indices.

        Examples
        ========

        >>> from sympy.tensor.tensor import TensorIndexType, tensor_indices, TensorSymmetry, TensorType, get_symmetric_group_sgs
        >>> Lorentz = TensorIndexType('Lorentz', dummy_fmt='L')
        >>> a, b, c, d = tensor_indices('a,b,c,d', Lorentz)
        >>> sym2 = TensorSymmetry(get_symmetric_group_sgs(2))
        >>> S2 = TensorType([Lorentz]*2, sym2)
        >>> A, B = S2('A,B')
        >>> t = A(a,b)*B(-b,c)
        >>> t
        A(a, L_0)*B(-L_0, c)
        >>> t.split()
        [A(a, L_0), B(-L_0, c)]


        """
        indices = self.get_indices()
        pos = 0
        components = self.components
        res = []
        for t in self.components:
            t1 = t(*indices[pos:pos + t.rank])
            pos += t.rank
            res.append(t1)
        res[0] = Tensor(self.coeff, res[0].components, res[0].free, res[0].dum, is_canon_bp=res[0]._is_canon_bp)
        return res

    def canon_args(self):
        """
        Returns (g, dummies, msym, v), the entries of `canonicalize`

        see `canonicalize` in tensor_can.py
        """
        # to be called after sorted_components
        from sympy.combinatorics.permutations import _af_new
        types = list(set(self.types))
        types.sort(key = lambda x: x.name)
        n = self.rank
        g = [None]*n + [n, n+1]
        pos = 0
        vpos = []
        components = self.components
        for t in self.components:
            vpos.append(pos)
            pos += t.rank
        for i, (indx, ipos, cpos) in enumerate(self.free):
            pos = vpos[cpos] + ipos
            g[pos] = i

        pos = len(self.free)
        j = len(self.free)
        dummies = []
        prev = None
        a = []
        msym = []
        for ipos1, ipos2, cpos1, cpos2 in self.dum:
            pos1 = vpos[cpos1] + ipos1
            pos2 = vpos[cpos2] + ipos2
            g[pos1] = j
            g[pos2] = j + 1
            j += 2
            typ = components[cpos1].index_types[ipos1]
            if typ != prev:
                if a:
                    dummies.append(a)
                a = [pos, pos + 1]
                prev = typ
                msym.append(typ.metric_sym)
            else:
                a.extend([pos, pos + 1])
            pos += 2
        if a:
            dummies.append(a)
        numtyp = []
        prev = None
        for t in components:
            if t == prev:
                numtyp[-1][1] += 1
            else:
                prev = t
                numtyp.append([prev, 1])
        v = []
        for h, n in numtyp:
            v.append((h.symmetry.base, h.symmetry.generators, n, h.commuting))
        return _af_new(g), dummies, msym, v

    def __mul__(self, other):
        #if not isinstance(other, Tensor):
        other = sympify(other)
        if not other.is_Tensor:
            coeff = self.coeff*other
            return Tensor(coeff, self.components, self.free, self.dum, is_canon_bp=self._is_canon_bp)
        if other.is_TensAdd:
            return TensAdd(*[self*x for x in other.args])

        components = self.components + other.components
        # find out which free indices of self and other are contracted
        free_dict1 = dict([(i.name, (pos, cpos, i)) for i, pos, cpos in self.free])
        free_dict2 = dict([(i.name, (pos, cpos, i)) for i, pos, cpos in other.free])

        free_names = set(free_dict1.keys()) & set(free_dict2.keys())
        # find the new `free` and `dum`
        nc1 = len(self.components)
        dum2 = [(i1, i2, c1 + nc1, c2 + nc1) for i1, i2, c1, c2 in other.dum]
        free1 = [(ind, i, c) for ind, i, c in self.free if ind.name not in free_names]
        free2 = [(ind, i, c + nc1) for ind, i, c in other.free if ind.name not in free_names]
        free = free1 + free2
        dum = self.dum + dum2
        for name in free_names:
            ipos1, cpos1, ind1 = free_dict1[name]
            ipos2, cpos2, ind2 = free_dict2[name]
            cpos2 += nc1
            if ind1.is_contravariant == ind2.is_contravariant:
                raise ValueError('wrong index contruction %s' % ind1)
            if ind1.is_contravariant:
                new_dummy = (ipos1, ipos2, cpos1, cpos2)
            else:
                new_dummy = (ipos2, ipos1, cpos2, cpos1)
            dum.append(new_dummy)
        coeff = self.coeff*other.coeff
        return Tensor(coeff, components, free, dum)


    def sorted_components(self):
        """
        Returns a tensor with sorted components
        """
        cv = zip(self.components, range(len(self.components)))
        sign = 1
        n = len(cv) - 1
        for i in range(n):
            for j in range(n, i, -1):
                c = cv[j-1][0].commutes_with(cv[j][0])
                if c == None:
                    continue
                if (cv[j-1][0].types, cv[j-1][0].name) > \
                        (cv[j][0].types, cv[j][0].name):
                    cv[j-1], cv[j] = cv[j], cv[j-1]
                    if c:
                        sign = -sign
        # perm_inv[new_pos] = old_pos
        components = [x[0] for x in cv]
        perm_inv = [x[1] for x in cv]
        perm = _af_invert(perm_inv)
        free = [(ind, i, perm[c]) for ind, i, c in self.free]
        dum = [(i1, i2, perm[c1], perm[c2]) for i1, i2, c1, c2 in self.dum]
        free.sort(key = lambda x: (x[0].tensortype, x[0].name))
        dum.sort(key = lambda x: components[x[2]].index_types[x[0]])
        if sign == -1:
            coeff = -self.coeff
        else:
            coeff = self.coeff
        t = Tensor(coeff, components, free, dum)
        return t

    def perm2tensor(self, g, canon_bp=False):
        """
        Returns the tensor corresponding to the permutation `g`

        g  permutation corrisponding to the tensor in the representation
        used in canonicalization

        canon_bp   if canon_bp is True, then `g` is the permutation
        corresponding to the canonical form of the tensor
        """
        from bisect import bisect_right
        vpos = []
        components = self.components
        pos = 0
        for t in self.components:
            vpos.append(pos)
            pos += t.rank
        free_indices = [x[0] for x in self.free]
        sorted_free = sorted(free_indices, key=lambda x:(x.tensortype, x.name))
        nfree = len(sorted_free)
        rank = self.rank
        indices = [None]*rank
        dum = [[None]*4 for i in range((rank - nfree)//2)]
        free = []
        icomp = -1
        for i in range(rank):
            if i in vpos:
                icomp += 1
                pos0 = i
            ipos = i - pos0
            gi = g[i]
            if gi < nfree:
                ind = sorted_free[gi]
                free.append((ind, ipos, icomp))
            else:
                j = gi - nfree
                idum, cov = divmod(j, 2)
                if cov:
                    dum[idum][1] = ipos
                    dum[idum][3] = icomp
                else:
                    dum[idum][0] = ipos
                    dum[idum][2] = icomp
        dum = [tuple(x) for x in dum]
        coeff = self.coeff
        if g[-1] != len(g) - 1:
            coeff = -coeff
        res = Tensor(coeff, components, free, dum, is_canon_bp=canon_bp)
        #if canon_bp:
        #    res._canon_bp = True
        return res

    def canon_bp(self):
        """
        canonicalize using the Butler-Portugal algorithm for canonicalization
        under monoterm symmetries.

        Examples
        ========
        >>> from sympy.tensor.tensor import TensorIndexType, tensor_indices, TensorSymmetry, get_symmetric_group_sgs, TensorType
        >>> Lorentz = TensorIndexType('Lorentz', dummy_fmt='L')
        >>> m0, m1, m2 = tensor_indices('m0,m1,m2', Lorentz)
        >>> sym2a = TensorSymmetry(get_symmetric_group_sgs(2, 1))
        >>> S2 = TensorType([Lorentz]*2, sym2a)
        >>> A = S2('A')
        >>> t = A(m0,-m1)*A(m1,-m2)*A(m2,-m0)
        >>> t.canon_bp()
        0
        """
        from sympy.combinatorics.tensor_can import canonicalize
        if self._is_canon_bp:
            return self
        t = self.sorted_components()
        g, dummies, msym, v = t.canon_args()
        can = canonicalize(g, dummies, msym, *v)
        if can == 0:
            return S.Zero
        return t.perm2tensor(can, True)


    def _pretty(self):
        indices = [str(ind) for ind in self.get_indices()]
        pos = 0
        a = []
        for t in self.components:
            a.append('%s(%s)' % (t.name, ', '.join(indices[pos:pos + t.rank])))
            pos += t.rank
        res = '*'. join(a)
        if self.coeff == S.One:
            return res
        elif self.coeff == -S.One:
            return '-%s' % res
        if self.coeff.is_Atom:
            return '%s*%s' % (self.coeff, res)
        else:
            return '(%s)*%s' %(self.coeff, res)



def canon_bp(p):
    """
    Butler-Portugal canonicalization
    """
    if p.is_Tensor:
        return p.canon_bp()
    if p.is_Add:
        return Add(*[canon_bp(x) for x in p.args])
    if p.is_Mul:
        return Mul(*[canon_bp(x) for x in p.args])
    return p

def tensor_mul(*a):
    """
    product of tensors
    """
    t = a[0]
    for tx in a[1:]:
        t = t*tx
    return t

def riemann_cyclic_replaceR(t_r):
    """
    R(m,n,p,q) -> 2/3*R(m,n,p,q) - 1/3*R(m,q,n,p) + 1/3*R(m,p,n,q)

    """
    free = sorted(t_r.free, key=lambda x: x[1])
    m, n, p, q = [x[0] for x in free]
    t0 = S(2)/3*t_r
    t1 = - S(1)/3*t_r.substitute_indices((m,m),(n,q),(p,n),(q,p))
    t2 = S(1)/3*t_r.substitute_indices((m,m),(n,p),(p,n),(q,q))
    t3 = t0 + t1 + t2
    return t3

def riemann_cyclic(t2):
    """
    replace each Riemann tensor with an equivalent expression
    satisfying the cyclic identity

    Examples
    ========

    >>> from sympy.tensor.tensor import TensorIndexType, tensor_indices, TensorSymmetry, TensorType, riemann_cyclic, riemann_bsgs
    >>> Lorentz = TensorIndexType('Lorentz', dummy_fmt='L')
    >>> i, j, k, l = tensor_indices('i,j,k,l', Lorentz)
    >>> symr = TensorSymmetry(riemann_bsgs)
    >>> R4 = TensorType([Lorentz]*4, symr)
    >>> R = R4('R')
    >>> t = R(i,j,k,l)*(R(-i,-j,-k,-l) - 2*R(-i,-k,-j,-l))
    >>> riemann_cyclic(t)
    0
    """
    a = t2.args
    a1 = [x.split() for x in a]
    a2 = [[riemann_cyclic_replaceR(tx) for tx in y] for y in a1]
    a3 = [tensor_mul(*v) for v in a2]
    t3 = TensAdd(*a3)
    if not t3:
        return t3
    else:
        return canon_bp(t3)