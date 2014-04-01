r"""
Functor construction for all spaces (artificial to make the coercion framework work)

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

from constructor                                 import FormsSpace, FormsRing

def get_base_ring(ring, var_name="d"):
    from sage.rings.fraction_field import is_FractionField
    from sage.rings.polynomial.polynomial_ring import is_PolynomialRing

    base_ring = ring
    if (is_FractionField(base_ring)):
        base_ring = base_ring.base()
    if (is_PolynomialRing(base_ring) and base_ring.ngens()==1 and base_ring.variable_name()==var_name):
        base_ring = base_ring.base()

    return base_ring


class FormsSpaceFunctor(ConstructionFunctor):
    from analytic_type import AnalyticType
    AT = AnalyticType()

    rank = 10

    def __init__(self, analytic_type, group, k, ep):
        Functor.__init__(self, Rings(), CommutativeAdditiveGroups())
        from space import canonical_parameters
        (self._group, R, self._k, self._ep) = canonical_parameters(group, ZZ, k, ep)

        self._analytic_type = self.AT(analytic_type)

    def __call__(self, R):
        if (isinstance(R, BaseFacade)):
            R = get_base_ring(R._ring)
            return FormsSpace(self._analytic_type, self._group, R, self._k, self._ep)
        else:
            R = get_base_ring(R)
            analytic_type = self._analytic_type.extend_by("holo")

            if (self._k == 0 and self._ep == 1):
                return FormsSpace(analytic_type, self._group, R, QQ(0), ZZ(1))
            else:
                return FormsRing(analytic_type, self._group, R, True)

    def __repr__(self):
        return "{}FormsFunctor(n={}, k={}, ep={})".format(self._analytic_type.analytic_space_name(), self._group.n, self._k, self._ep)

    def merge(self, other):
        if (self == other):
            return self
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

    def __cmp__(self, other):
        if    ( type(self)          == type(other)\
            and self._group         == other._group\
            and self._analytic_type == other._analytic_type\
            and self._k             == other._k\
            and self._ep            == other._ep ):
                return 0
        else:
            return -1
    
class FormsRingFunctor(ConstructionFunctor):
    from analytic_type import AnalyticType
    AT = AnalyticType()

    rank = 10

    def __init__(self, analytic_type, group, red_hom):
        Functor.__init__(self, Rings(), Rings())
        from graded_ring import canonical_parameters
        (self._group, R, red_hom) = canonical_parameters(group, ZZ, red_hom)
        self._red_hom = bool(red_hom)
        self._analytic_type = self.AT(analytic_type)

    def __call__(self, R):
        if (isinstance(R, BaseFacade)):
            R = get_base_ring(R._ring)
            return FormsRing(self._analytic_type, self._group, R, self._red_hom)
        else:
            R = get_base_ring(R)
            analytic_type = self._analytic_type.extend_by("holo")
            return FormsRing(analytic_type, self._group, R, self._red_hom)

    def __repr__(self):
        if (self._red_hom):
            red_arg = ", red_hom=True"
        else:
            red_arg = ""
        return "{}FormsRingFunctor(n={}{})".format(self._analytic_type.analytic_space_name(), self._group.n, red_arg)

    def merge(self, other):
        if (self == other):
            return self
        elif isinstance(other, FormsSpaceFunctor):
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

    def __cmp__(self, other):
        if    ( type(self)          == type(other)\
            and self._group         == other._group\
            and self._analytic_type == other._analytic_type\
            and self._red_hom       == other._red_hom ):
                return 0
        else:
            return -1


from sage.structure.unique_representation import UniqueRepresentation
class BaseFacade(Parent, UniqueRepresentation):
    def __init__(self, ring):
        Parent.__init__(self, facade=ring, category=Rings())
        self._ring = get_base_ring(ring)
        # The BaseFacade(R) coerces/embeds into R, used in pushout
        self.register_embedding(self.Hom(self._ring,Sets())(lambda x: x))
    def __repr__(self):
        return "BaseFacade({})".format(self._ring)
