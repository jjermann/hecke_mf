r"""
Functor construction for all spaces

AUTHORS:

- Jonas Jermann (2013): initial version

"""

#*****************************************************************************
#       Copyright (C) 2013 Jonas Jermann <jjermann2@gmail.com>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#  as published by the Free Software Foundation; either version 2 of
#  the License, or (at your option) any later version.
#                  http://www.gnu.org/licenses/
#*****************************************************************************

from sage.rings.all import ZZ, QQ, infinity

from sage.categories.functor                     import Functor
from sage.categories.pushout                     import ConstructionFunctor
from sage.categories.sets_cat                    import Sets
from sage.structure.parent                       import Parent
from sage.categories.commutative_additive_groups import CommutativeAdditiveGroups
from sage.categories.rings                       import Rings

from constructor                                 import FormsSubSpace, FormsSpace, FormsRing


def get_base_ring(ring, var_name="d"):
    r"""
    Return the base ring of the given ``ring``:

    If ``ring`` is of the form ``FractionField(PolynomialRing(R,'d'))``:
    Return ``R``.

    If ``ring`` is of the form ``FractionField(R)``:
    Return ``R``.

    If ``ring`` is of the form ``PolynomialRing(R,'d')``:
    Return ``R``.
    
    Otherwise return ``ring``.

    The base ring is used in the construction of the correponding
    ``FormsRing`` or ``FormsSpace``. In particular in the construction
    of holomorphic forms of degree (0, 1). For (binary)
    operations a general ring element is considered (coerced to)
    a (constant) holomorphic form of degree (0, 1)
    whose construction should be based on the returned base ring
    (and not on ``ring``!).

    If ``var_name`` (default: "d") is specified then this variable
    name is used for the polynomial ring.
    """

    #from sage.rings.fraction_field import is_FractionField
    from sage.rings.polynomial.polynomial_ring import is_PolynomialRing
    from sage.categories.pushout import FractionField as FractionFieldFunctor

    base_ring = ring
    #if (is_FractionField(base_ring)):
    #    base_ring = base_ring.base()
    if (base_ring.construction() and base_ring.construction()[0] == FractionFieldFunctor()):
        base_ring = base_ring.construction()[1]
    if (is_PolynomialRing(base_ring) and base_ring.ngens()==1 and base_ring.variable_name()==var_name):
        base_ring = base_ring.base()
    if (base_ring.construction() and base_ring.construction()[0] == FractionFieldFunctor()):
        base_ring = base_ring.construction()[1]

    return base_ring


def ConstantFormsSpaceFunctor(group):
    r"""
    Construction functor for the space of constant forms.

    When determening a common parent between a ring
    and a forms ring or space this functor is first
    applied to the ring.
    """

    return FormsSpaceFunctor("holo", group, QQ(0), ZZ(1))


class FormsSubSpaceFunctor(ConstructionFunctor):
    r"""
    Construction functor for forms sub spaces.

    Note: When the base ring is not a ``BaseFacade``
    the functor is first merged with the ConstantFormsSpaceFunctor.
    This case occurs in the pushout constructions
    (when trying to find a common parent
    between a forms subspace and a ring which
    is not a ``BaseFacade``).
    """

    from analytic_type import AnalyticType
    AT = AnalyticType()

    rank = 10

    def __init__(self, analytic_type, group, k, ep, basis):
        r"""
        Construction functor for the forms sub space
        for the given ``basis`` inside the ambient space
        which is determined by the given ``analytic_type``,
        ``group``, weight ``k`` and multiplier ``ep``.

        See :meth:`__call__` for a description of the functor.

        INPUT:

        - ``analytic_type``   - An element of ``AnalyticType()``.
        - ``group``           - A Hecke Triangle group.
        - ``k``               - A rational number, the weight of the space.
        - ``ep``              - ``1`` or ``-1``, the multiplier of the space.
        - ``basis``           - A list of elements of a corresponding
                                ambient space over some base ring.

        OUTPUT:
 
        The construction functor for the corresponding forms sub space.
        """

        Functor.__init__(self, Rings(), CommutativeAdditiveGroups())
        from space import canonical_parameters
        (self._group, R, self._k, self._ep) = canonical_parameters(group, ZZ, k, ep)

        self._analytic_type = self.AT(analytic_type)
        self._basis = basis
        #self._basis_ring = 
        #on call check if there is a coercion from self._basis_ring to R

    def __call__(self, R):
        r"""
        If ``R`` is a ``BaseFacade(S)`` then return the corresponding
        forms subspace with base ring ``get_base_ring(S)``.
        For this it is required that the base ring of the basis coerces
        into the new base ring.
        
        If not then we first merge the functor with the ConstantFormsSpaceFunctor.
        """

        if (isinstance(R, BaseFacade)):
            R = get_base_ring(R._ring)
            return FormsSubSpace(self._analytic_type, self._group, R, self._k, self._ep, self._basis)
        else:
            R = BaseFacade(get_base_ring(R))
            merged_functor = self.merge(ConstantFormsSpaceFunctor(self._group))
            return merged_functor(R)

    def __repr__(self):
        r"""  
        Return the string representation of ``self``.
        """

        return "FormsSubSpaceFunctor for the basis {}".format(self._basis)

    def merge(self, other):
        r"""
        Return the merged functor of ``self`` and ``other``.

        It is only possible to merge instances of
        ``FormsSubSpaceFunctor``, ``FormsSpaceFunctor`` and
        ``FormsRingFunctor``. Also only if they share the same group.

        The analytic type of the merged functor is the extension
        of the two analytic types of the functors.
        The ``red_hom`` parameter of the merged functor
        is the logical ``and`` of the two corresponding ``red_hom``
        parameters (where a forms space is assumed to have it
        set to ``True``).
    
        Two ``FormsSubSpaceFunctor`` are merged to one with
        a united basis and analytic type in case the weight and
        multiplier agree. Otherwise the corresponding (extended)
        ``FormsSpaceFunctor`` is returned.
        
        If only one ``FormsSubSpaceFunctor`` is involved then
        it is treated like a ``FormsSpaceFunctor`` for the ambient space.
 
        Two ``FormsSpaceFunctor`` with different (k,ep)
        are merged to a corresponding ``FormsRingFunctor``.
        Otherwise the corresponding (extended) ``FormsSpaceFunctor``
        is returned.

        A ``FormsSpaceFunctor`` and ``FormsRingFunctor``
        are merged to a corresponding (extended) ``FormsRingFunctor``.

        Two ``FormsRingFunctors`` are merged to the corresponding
        (extended) ``FormsRingFunctor``.
        """

        if (self == other):
            return self
        elif isinstance(other, FormsSubSpaceFunctor):
            if not (self._group == other._group):
                return None
            analytic_type = self._analytic_type + other._analytic_type
            if (self._k == other._k) and (self._ep == other._ep):
                if (self._basis == other._basis):
                    basis = self._basis
                    return FormsSubSpaceFunctor(analytic_type, self._group, self._k, self._ep, basis)
                else:
                    #TODO: Or combine the basis to a new basis (which one?)
                    #basis = self._basis + other._basis
                    #return FormsSubSpaceFunctor(analytic_type, self._group, self._k, self._ep, basis)
                    return FormsSpaceFunctor(analytic_type, self._group, self._k, self._ep)
            else:
                return FormsRingFunctor(analytic_type, self._group, True)
        elif isinstance(other, FormsSpaceFunctor):
            if not (self._group == other._group):
                return None
            analytic_type = self._analytic_type + other._analytic_type
            if (self._k == other._k) and (self._ep == other._ep):
                return FormsSpaceFunctor(analytic_type, self._group, self._k, self._ep)
            else:
                return FormsRingFunctor(analytic_type, self._group, True)
        elif isinstance(other, FormsRingFunctor):
            if not (self._group == other._group):
                return None
            red_hom = other._red_hom
            analytic_type = self._analytic_type + other._analytic_type
            return FormsRingFunctor(analytic_type, self._group, red_hom)

    def __eq__(self, other):
        r"""
        Compare ``self`` and ``other``.
        """

        if    ( type(self)          == type(other)\
            and self._group         == other._group\
            and self._analytic_type == other._analytic_type\
            and self._k             == other._k\
            and self._ep            == other._ep\
            and self._basis         == other._basis ):
                return True
        else:
            return False
    


class FormsSpaceFunctor(ConstructionFunctor):
    r"""
    Construction functor for forms spaces.

    Note: When the base ring is not a ``BaseFacade``
    the functor is first merged with the ConstantFormsSpaceFunctor.
    This case occurs in the pushout constructions
    (when trying to find a common parent
    between a forms space and a ring which
    is not a ``BaseFacade``).
    """

    from analytic_type import AnalyticType
    AT = AnalyticType()

    rank = 10

    def __init__(self, analytic_type, group, k, ep):
        r"""
        Construction functor for the forms space
        (or forms ring, see above) with
        the given ``analytic_type``, ``group``,
        weight ``k`` and multiplier ``ep``.

        See :meth:`__call__` for a description of the functor.

        INPUT:

        - ``analytic_type``   - An element of ``AnalyticType()``. 
        - ``group``           - A Hecke Triangle group.
        - ``k``               - A rational number, the weight of the space.
        - ``ep``              - ``1`` or ``-1``, the multiplier of the space.

        OUTPUT:
 
        The construction functor for the corresponding forms space/ring.
        """

        Functor.__init__(self, Rings(), CommutativeAdditiveGroups())
        from space import canonical_parameters
        (self._group, R, self._k, self._ep) = canonical_parameters(group, ZZ, k, ep)

        self._analytic_type = self.AT(analytic_type)

    def __call__(self, R):
        r"""
        If ``R`` is a ``BaseFacade(S)`` then return the corresponding
        forms space with base ring ``get_base_ring(S)``.
        
        If not then we first merge the functor with the ConstantFormsSpaceFunctor.
        """

        if (isinstance(R, BaseFacade)):
            R = get_base_ring(R._ring)
            return FormsSpace(self._analytic_type, self._group, R, self._k, self._ep)
        else:
            R = BaseFacade(get_base_ring(R))
            merged_functor = self.merge(ConstantFormsSpaceFunctor(self._group))
            return merged_functor(R)

    def __repr__(self):
        r"""  
        Return the string representation of ``self``.
        """

        return "{}FormsFunctor(n={}, k={}, ep={})".format(self._analytic_type.analytic_space_name(), self._group.n, self._k, self._ep)

    def merge(self, other):
        r"""
        Return the merged functor of ``self`` and ``other``.

        It is only possible to merge instances of
        ``FormsSubSpaceFunctor``, ``FormsSpaceFunctor`` and
        ``FormsRingFunctor``. Also only if they share the same group.

        The analytic type of the merged functor is the extension
        of the two analytic types of the functors.
        The ``red_hom`` parameter of the merged functor
        is the logical ``and`` of the two corresponding ``red_hom``
        parameters (where a forms space is assumed to have it
        set to ``True``).
    
        Two ``FormsSubSpaceFunctor`` are merged to one with
        a united basis and analytic type in case the weight and
        multiplier agree. Otherwise the corresponding (extended)
        ``FormsSpaceFunctor`` is returned.
        
        If only one ``FormsSubSpaceFunctor`` is involved then
        it is treated like a ``FormsSpaceFunctor`` for the ambient space.

        Two ``FormsSpaceFunctor`` with different (k,ep)
        are merged to a corresponding ``FormsRingFunctor``.
        Otherwise the corresponding (extended) ``FormsSpaceFunctor``
        is returned.

        A ``FormsSpaceFunctor`` and ``FormsRingFunctor``
        are merged to a corresponding (extended) ``FormsRingFunctor``.

        Two ``FormsRingFunctors`` are merged to the corresponding
        (extended) ``FormsRingFunctor``.
        """

        if (self == other):
            return self
        elif isinstance(other, FormsSubSpaceFunctor) or isinstance(other, FormsSpaceFunctor):
            if not (self._group == other._group):
                return None
            analytic_type = self._analytic_type + other._analytic_type
            if (self._k == other._k) and (self._ep == other._ep):
                return FormsSpaceFunctor(analytic_type, self._group, self._k, self._ep)
            else:
                return FormsRingFunctor(analytic_type, self._group, True)
        elif isinstance(other, FormsRingFunctor):
            if not (self._group == other._group):
                return None
            red_hom = other._red_hom
            analytic_type = self._analytic_type + other._analytic_type
            return FormsRingFunctor(analytic_type, self._group, red_hom)

    def __eq__(self, other):
        r"""
        Compare ``self`` and ``other``.
        """

        if    ( type(self)          == type(other)\
            and self._group         == other._group\
            and self._analytic_type == other._analytic_type\
            and self._k             == other._k\
            and self._ep            == other._ep ):
                return True
        else:
            return False
    
class FormsRingFunctor(ConstructionFunctor):
    r"""
    Construction functor for forms rings.

    Note: When the base ring is not a ``BaseFacade``
    the functor is first merged with the ConstantFormsSpaceFunctor.
    This case occurs in the pushout constructions.
    (when trying to find a common parent
    between a forms ring and a ring which
    is not a ``BaseFacade``).
    """

    from analytic_type import AnalyticType
    AT = AnalyticType()

    rank = 10

    def __init__(self, analytic_type, group, red_hom):
        r"""
        Construction functor for the forms ring
        with the given ``analytic_type``, ``group``
        and variable ``red_hom``

        See :meth:`__call__` for a description of the functor.

        INPUT:
        
                                                                                
                                                                            
        - ``analytic_type``   - An element of ``AnalyticType()``. 
        - ``group``           - A Hecke Triangle group.
        - ``red_hom``         - A boolean variable for the parameter ``red_hom``
                                (also see ``FormsRing_abstract``).

        OUTPUT:
 
        The construction functor for the corresponding forms ring.
        """

        Functor.__init__(self, Rings(), Rings())
        from graded_ring import canonical_parameters
        (self._group, R, red_hom) = canonical_parameters(group, ZZ, red_hom)
        self._red_hom = bool(red_hom)
        self._analytic_type = self.AT(analytic_type)

    def __call__(self, R):
        r"""
        If ``R`` is a ``BaseFacade(S)`` then return the corresponding
        forms ring with base ring ``get_base_ring(S)``.
        
        If not then we first merge the functor with the ConstantFormsSpaceFunctor.
        """

        if (isinstance(R, BaseFacade)):
            R = get_base_ring(R._ring)
            return FormsRing(self._analytic_type, self._group, R, self._red_hom)
        else:
            R = BaseFacade(get_base_ring(R))
            merged_functor = self.merge(ConstantFormsSpaceFunctor(self._group))
            return merged_functor(R)

    def __repr__(self):
        r"""  
        Return the string representation of ``self``.
        """

        if (self._red_hom):
            red_arg = ", red_hom=True"
        else:
            red_arg = ""
        return "{}FormsRingFunctor(n={}{})".format(self._analytic_type.analytic_space_name(), self._group.n, red_arg)

    def merge(self, other):
        r"""
        Return the merged functor of ``self`` and ``other``.

        It is only possible to merge instances of
        ``FormsSubSpaceFunctor``, ``FormsSpaceFunctor`` and
        ``FormsRingFunctor``. Also only if they share the same group.

        The analytic type of the merged functor is the extension
        of the two analytic types of the functors.
        The ``red_hom`` parameter of the merged functor
        is the logical ``and`` of the two corresponding ``red_hom``
        parameters (where a forms space is assumed to have it
        set to ``True``).
    
        Two ``FormsSubSpaceFunctor`` are merged to one with
        a united basis and analytic type in case the weight and
        multiplier agree. Otherwise the corresponding (extended)
        ``FormsSpaceFunctor`` is returned.
        
        If only one ``FormsSubSpaceFunctor`` is involved then
        it is treated like a ``FormsSpaceFunctor`` for the ambient space.

        Two ``FormsSpaceFunctor`` with different (k,ep)
        are merged to a corresponding ``FormsRingFunctor``.
        Otherwise the corresponding (extended) ``FormsSpaceFunctor``
        is returned.

        A ``FormsSpaceFunctor`` and ``FormsRingFunctor``
        are merged to a corresponding (extended) ``FormsRingFunctor``.

        Two ``FormsRingFunctors`` are merged to the corresponding
        (extended) ``FormsRingFunctor``.
        """

        if (self == other):
            return self
        elif isinstance(other, FormsSubSpaceFunctor) or isinstance(other, FormsSpaceFunctor):
            if not (self._group == other._group):
                return None
            red_hom = self._red_hom
            analytic_type = self._analytic_type + other._analytic_type
            return FormsRingFunctor(analytic_type, self._group, red_hom)
        elif isinstance(other, FormsRingFunctor):
            if not (self._group == other._group):
                return None
            red_hom = self._red_hom & other._red_hom
            analytic_type = self._analytic_type + other._analytic_type
            return FormsRingFunctor(analytic_type, self._group, red_hom)

    def __eq__(self, other):
        r"""
        Compare ``self`` and ``other``.
        """

        if    ( type(self)          == type(other)\
            and self._group         == other._group\
            and self._analytic_type == other._analytic_type\
            and self._red_hom       == other._red_hom ):
                return True
        else:
            return False


from sage.structure.unique_representation import UniqueRepresentation
class BaseFacade(Parent, UniqueRepresentation):
    r"""
    BaseFacade of a ring.

    This class is used to distinguish the construction of
    constant elements (modular forms of weight 0) over the given ring
    and the construction of ``FormsRing`` or ``FormsSpace``
    based on the BaseFacade of the given ring.

    If that distinction was not made then ring elements
    couldn't be considered as constant modular forms
    in e.g. binary operations. Instead the coercion model would
    assume that the ring element lies in the common parent
    of the ring element and e.g. a ``FormsSpace`` which
    would give the ``FormsSpace`` over the ring. However
    this is not correct, the ``FormsSpace`` might
    (and probably will) not even contain the (constant)
    ring element. Hence we use the ``BaseFacade`` to
    distinguish the two cases.

    Since the ``BaseFacade`` of a ring embedds into that ring
    a common base (resp. a coercion) between the two (or even a
    more general ring) can be found, namely the ring
    (not the ``BaseFacade`` of it).
    """

    def __init__(self, ring):
        r"""
        BaseFacade of ``ring`` (see above).
        """

        Parent.__init__(self, facade=ring, category=Rings())
        self._ring = get_base_ring(ring)
        # The BaseFacade(R) coerces/embeds into R, used in pushout
        self.register_embedding(self.Hom(self._ring,Sets())(lambda x: x))

    def __repr__(self):
        r"""  
        Return the string representation of ``self``.
        """

        return "BaseFacade({})".format(self._ring)
