r"""
Modular forms for Hecke triangle groups

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
from sage.rings.power_series_ring import is_PowerSeriesRing
from sage.rings.laurent_series_ring import is_LaurentSeriesRing

from sage.misc.cachefunc import cached_method

from abstract_ring import FormsRing_abstract
from series_constructor import MFSeriesConstructor


class FormsSpace_abstract(FormsRing_abstract):
    """
    Abstract space for (Hecke) forms.
    """
    from element import FormsElement
    Element = FormsElement

    def __init__(self, group, base_ring, k, ep):
        r"""
        Abstract space for (Hecke) modular forms.

        INPUT:

        - ``group``       - The Hecke triangle group (default: ``HeckeTriangleGroup(3)``)
        - ``k``           - The weight (default: ``0``)
        - ``ep``          - The epsilon (default: ``None``).
                            If ``None``, then k*(n-2) has to be divisible by 2 and
                            ep=(-1)^(k*(n-2)/2) is used.
        - ``base_ring``   - The base_ring (default: ``ZZ``).

        OUTPUT:

        The corresponding abstract space of (Hecke) forms.
        """

        from space import canonical_parameters
        (group, base_ring, k, ep) = canonical_parameters(group, base_ring, k, ep)

        super(FormsSpace_abstract, self).__init__(group=group, base_ring=base_ring, red_hom=True)
        #self.register_embedding(self.hom(lambda f: f.parent().graded_ring()(f), codomain=self.graded_ring()))

        self._weight = k
        self._ep = ep
        (self._l1,self._l2) = self.weight_parameters()
        self._ambient_module = None

    def _repr_(self):
        """
        Return the string representation of ``self``.
        """
        return "{}Forms(n={}, k={}, ep={}) over {}".format(self._analytic_type.analytic_space_name(), self._group.n, self._weight, self._ep, self._base_ring)

    def _latex_(self):
        r"""
        Return the LaTeX representation of ``self``.
        """
        from sage.misc.latex import latex
        return "{}_{{ n={} }}({},\ {})({})".format(self._analytic_type.latex_space_name(), self._group.n, self._weight, self._ep, latex(self._base_ring))

    def __cmp__(self, other):
        if (super(FormsSpace_abstract, self).__cmp__(other)==0 and self._weight==other._weight and self._ep==other._ep):
            return 0
        else:
            return -1

    def _element_constructor_(self,x):
        from graded_ring_element import FormsRingElement
        if isinstance(x, FormsRingElement):
            x = x._rat
        elif hasattr(x, 'parent'):
            parent = x.parent()
            # This assumes that the series corresponds to a weakly holomorphic modular form!
            # But the construction method (with the assumption) may also be used for more general form spaces...
            if (is_LaurentSeriesRing(parent) or is_PowerSeriesRing(parent)):
                return self.construct_form(x)
            elif self.ambient_module() and self.ambient_module().has_coerce_map_from(parent):
                return self.element_from_coordinates(x)
        x = (self.rat_field())(x)
        return self.element_class(self,x)
    def _coerce_map_from_(self,S):
        from space import ZeroForm
        if   (  isinstance(S, ZeroForm)):
            return True
        elif (  isinstance(S, FormsSpace_abstract)\
            and self.graded_ring().has_coerce_map_from(S.graded_ring())\
            and S.weight()    == self._weight\
            and S.ep()        == self._ep ):
                return True
        elif (self.AT("holo") <= self._analytic_type\
            and self._weight  == 0\
            and self._ep      == 1\
            and self.coeff_ring().has_coerce_map_from(S) ):
                return True
        else:
            return False

    def change_ring(self, new_base_ring):
        return self.__class__.__base__(self.group(), new_base_ring, True, self.weight(), self.ep())

    def construction(self):
        from functors import FormsSpaceFunctor, BaseFacade
        return FormsSpaceFunctor(self._analytic_type, self._group, self._weight, self._ep), BaseFacade(self._base_ring)

    @cached_method
    def weight(self):
        return self._weight
    @cached_method
    def ep(self):
        return self._ep
    @cached_method
    def ambient_module(self):
        return self._ambient_module
    def element_from_coordinates(self, vec, basis=None):
        if not self.ambient_module():
            raise Exception("No _ambient_module defined for {}".format(self))
        vec = self.ambient_module()(vec)
        if basis==None:
            basis = self.gens()
        # TODO: allow several ways to specify a basis, e.g. also a basis in the vector space?
        assert(len(basis) == len(vec))
        # this also handles the trivial case (dimension 0)
        return self(sum([vec[k]*basis[k] for k in range(0, len(vec))]))


    def homogeneous_space(self, k, ep):
        assert(k==self._weight and ep==self._ep)
        return self

    def weight_parameters(self):
        n = self._group.n
        k = self._weight
        ep = self._ep
        num = (k-(1-ep)*ZZ(n)/ZZ(n-2))*ZZ(n-2)/ZZ(4)

        if (num.is_integral()):
            num = ZZ(num)
            l2 = num%n
            l1 = ((num-l2)/n).numerator()
        else:
            raise Exception('Invalid resp. non-occuring weight!')
        return (l1,l2)

    def aut_factor(self,gamma,t):
        if (gamma == self._group.T or gamma == self._group.T.inverse()):
            return 1
        elif (gamma == self._group.S or gamma == -self._group.S):
            return self._ep*(t/AlgebraicField()(i))**self._weight
        else:
            raise NotImplementedError

    @cached_method
    def F_simple(self):
        (x,y,z,d) = self.rat_field().gens()

        finf_pol = d*(x**self._group.n - y**2)
        rat = finf_pol**self._l1 * x**self._l2 * y**(ZZ(1-self._ep)/ZZ(2))

        if (self._l1 > 0):
            new_space = self.extend_type("cusp")
        elif (self._l1 == 0):
            new_space = self.extend_type("holo")
        else:
            new_space = self.extend_type("weak")

        return new_space(rat)

    def Faber_pol(self, m, fix_d=False, d_num_prec=ZZ(53)):
        m = ZZ(m)
        if (m < -self._l1):
            raise Exception("Invalid basis index: {}<{}!".format(m,-self._l1))

        prec          = 2*self._l1+m+1
        SC            = MFSeriesConstructor(self._group, self.base_ring(), prec,fix_d, d_num_prec)
        q             = SC.q()
        d             = SC.d()
        qseries_ring  = SC.qseries_ring()

        simple_qexp   = self.F_simple().q_expansion(prec=prec, fix_d=fix_d, d_num_prec=d_num_prec)
        J_qexp        = self.J_inv().q_expansion(prec=m + self._l1, fix_d=fix_d, d_num_prec=d_num_prec)

        # The precision could be infinity, otherwise we could do this:
        #assert(temp_reminder.prec() == 1)
        temp_reminder = (1 / simple_qexp / q**m).add_bigoh(1)

        fab_pol       = qseries_ring([])
        while (len(temp_reminder.coefficients()) > 0):
            temp_coeff     = temp_reminder.coefficients()[0]
            temp_exp       = -temp_reminder.exponents()[0]
            fab_pol       += temp_coeff*(q/d)**temp_exp

            temp_reminder -= temp_coeff*(J_qexp/d)**temp_exp
            # The first term is zero only up to numerical errors,
            # so we manually have to remove it
            if (not SC.is_exact()):
                temp_reminder=temp_reminder.truncate_neg(-temp_exp+1)

        return fab_pol.polynomial()

    # For j_inv (normalized by Fourier coefficient)
    # very similar to Faber_pol: faber_pol(q)=Faber_pol(d*q)
    def faber_pol(self, m, fix_d=False, d_num_prec=ZZ(53)):
        m = ZZ(m)
        if (m < -self._l1):
            raise Exception("Invalid basis index: {}<{}!".format(m,-self._l1))

        prec          = 2*self._l1+m+1
        SC            = MFSeriesConstructor(self._group, self.base_ring(), prec,fix_d, d_num_prec)
        q             = SC.q()
        d             = SC.d()
        qseries_ring  = SC.qseries_ring()

        simple_qexp   = self.F_simple().q_expansion(prec=prec, fix_d=fix_d, d_num_prec=d_num_prec)
        j_qexp        = self.j_inv().q_expansion(prec=m + self._l1, fix_d=fix_d, d_num_prec=d_num_prec)

        # The precision could be infinity, otherwise we could do this:
        #assert(temp_reminder.prec() == 1)
        temp_reminder = (1 / simple_qexp / q**m).add_bigoh(1)

        fab_pol       = qseries_ring([])
        while (len(temp_reminder.coefficients()) > 0):
            temp_coeff     = temp_reminder.coefficients()[0]
            temp_exp       = -temp_reminder.exponents()[0]
            fab_pol       += temp_coeff*q**temp_exp

            temp_reminder -= temp_coeff*j_qexp**temp_exp
            # The first term is zero only up to numerical errors,
            # so we manually have to remove it
            if (not SC.is_exact()):
                temp_reminder=temp_reminder.truncate_neg(-temp_exp+1)

        return fab_pol.polynomial()

    def F_basis_pol(self, m):
        (x,y,z,d) = self.rat_field().gens()

        n        = self._group.n
        finf_pol = d*(x**n-y**2)
        jinv_pol = x**n/(x**n-y**2)
        rat      = finf_pol**self._l1 * x**self._l2 * y**(ZZ(1-self._ep)/ZZ(2)) * self.Faber_pol(m)(jinv_pol)

        #return self(self.F_simple()*self.Faber_pol(m)(self.graded_ring().J_inv()))
        return rat

    def F_basis(self, m):
        if (m < 0):
            new_space = self.extend_type("cusp")
        elif (m == 0):
            new_space = self.extend_type("holo")
        else:
            new_space = self.extend_type("weak")

        return new_space(self.F_basis_pol(m))

    # TODO: This only works for weakly holomorphic modular forms!
    def construct_form(self, laurent_series):
        if (laurent_series.prec() < self._l1+1):
            raise Exception('Insufficient precision!')

        laurent_series = laurent_series.add_bigoh(self._l1+1)
        coefficients   = laurent_series.coefficients()
        exponents      = laurent_series.exponents()

        if (len(coefficients) == 0):
            return self(0)

        rat = sum([\
                  coefficients[j] * self.F_basis_pol(-exponents[j])\
                  for j in range(ZZ(0), ZZ(len(coefficients)))
              ])

        return self(rat)


    # DEFAULT METHODS (should be overwritten in concrete classes)

    def _an_element_(self):
        # this seems ok, so might as well leave it as is for everything
        return self(ZZ(0))
        #return self.F_simple()

    @cached_method
    def dimension(self):
        """
        Return the dimension of the space.
        """
        return infinity
    def degree(self):
        return self.dimension()
    # where this makes sense, this should/must return the coordinate vector
    # in self._ambient_module with respect to self.gens()
    def coordinate_vector(self, v):
        raise NotImplementedError
    def gens(self):
        raise NotImplementedError
    def gen(self, k=0):
        k = ZZ(k)
        if k>=0 and k < self.dimension():
            return self.gens()[k]
        else:
            raise Exception("Invalid index: k={} does not satisfy 0 <= k <= {}!".format(k, self.dimension()))
