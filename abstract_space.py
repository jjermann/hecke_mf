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
from sage.modules.free_module_element import is_FreeModuleElement

from sage.misc.cachefunc import cached_method

from abstract_ring import FormsRing_abstract
from series_constructor import MFSeriesConstructor


class FormsSpace_abstract(FormsRing_abstract):
    r"""
    Abstract (Hecke) forms space.

    This should never be called directly. Instead one should
    instantiate one of the derived classes of this class. 
    """

    from element import FormsElement
    Element = FormsElement

    def __init__(self, group, base_ring, k, ep):
        r"""
        Abstract (Hecke) forms space.

        INPUT:

        - ``group``       - The Hecke triangle group (default: ``HeckeTriangleGroup(3)``)
        - ``k``           - The weight (default: ``0``)
        - ``ep``          - The epsilon (default: ``None``).
                            If ``None``, then k*(n-2) has to be divisible by 2 and
                            ep=(-1)^(k*(n-2)/2) is used.
        - ``base_ring``   - The base_ring (default: ``ZZ``).

        OUTPUT:

        The corresponding abstract (Hecke) forms space.
        """

        from space import canonical_parameters
        (group, base_ring, k, ep) = canonical_parameters(group, base_ring, k, ep)

        super(FormsSpace_abstract, self).__init__(group=group, base_ring=base_ring, red_hom=True)
        #self.register_embedding(self.hom(lambda f: f.parent().graded_ring()(f), codomain=self.graded_ring()))

        self._weight = k
        self._ep = ep
        (self._l1,self._l2) = self.weight_parameters()
        self._module = None
        self._ambient_space = self

    def _repr_(self):
        r"""
        Return the string representation of ``self``.
        """

        return "{}Forms(n={}, k={}, ep={}) over {}".format(self._analytic_type.analytic_space_name(), self._group.n, self._weight, self._ep, self._base_ring)

    def _latex_(self):
        r"""
        Return the LaTeX representation of ``self``.
        """

        from sage.misc.latex import latex
        return "{}_{{ n={} }}({},\ {})({})".format(self._analytic_type.latex_space_name(), self._group.n, self._weight, self._ep, latex(self._base_ring))

    def _element_constructor_(self, x):
        r"""
        Return ``x`` coerced into this forms space.
        """

        from graded_ring_element import FormsRingElement
        if isinstance(x, FormsRingElement):
            return self.element_class(self, x._rat)
        if hasattr(x, 'parent') and (is_LaurentSeriesRing(x.parent()) or is_PowerSeriesRing(x.parent())):
            # This assumes that the series corresponds to a weakly holomorphic modular form!
            # But the construction method (with the assumption) may also be used for more general form spaces...
            return self.construct_form(x)
        if is_FreeModuleElement(x) and (self.module() == x.parent() or self.ambient_module() == x.parent()):
            return self.element_from_ambient_coordinates(x)
        if (not self.is_ambient()) and (isinstance(x, list) or isinstance(x, tuple) or is_FreeModuleElement(x)) and len(x) == self.rank():
            try:
                return self.element_from_coordinates(x)
            except ArithmeticError, TypeError:
                pass
        if hasattr(x, 'parent') and self.ambient_module() and self.ambient_module().has_coerce_map_from(x.parent()):
            return self.element_from_ambient_coordinates(self.ambient_module(x))
        if (isinstance(x,list) or isinstance(x, tuple)) and len(x) == self.degree():
            try:
                return self.element_from_ambient_coordinates(x)
            except ArithmeticError, TypeError:
                pass

        return self.element_class(self, x)

    def _coerce_map_from_(self, S):
        r"""
        Return whether or not there exists a coercion from ``S`` to ``self``.
        """

        from space import ZeroForm
        if   (  isinstance(S, ZeroForm)):
            return True
        elif ( not self.is_ambient()):
            if (self == S):
                return True
            else:
                return False
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

    def is_ambient(self):
        r"""
        Return whether ``self`` is an ambient space.
        """

        return self._ambient_space == self

    def ambient_space(self):
        r"""
        Return the ambient space of self.
        """

        return self._ambient_space

    def module(self):
        r"""
        Return the module associated to self.
        """

        return self._module

    def ambient_module(self):
        r"""
        Return the module associated to the ambient space of self.
        """

        return self._ambient_space._module

    def subspace(self, basis):
        r"""
        Return the subspace of ``self`` generated by ``basis``.
        """

        from subspace import SubSpaceForms
        return SubSpaceForms(self, basis)

    def change_ring(self, new_base_ring):
        r"""
        Return the same space as ``self`` but over a new base ring ``new_base_ring``.
        """

        return self.__class__.__base__(self.group(), new_base_ring, self.weight(), self.ep())

    def construction(self):
        r"""
        Return a functor that constructs ``self`` (used by the coercion machinery).

        EXAMPLE:: 

        sage: from space import QModularForms
        sage: QModularForms(k=2).construction()
        (QuasiModularFormsFunctor(n=3, k=2, ep=-1), BaseFacade(Integer Ring))
        """

        from functors import FormsSubSpaceFunctor, FormsSpaceFunctor, BaseFacade
        if (self.is_ambient()):
            return FormsSpaceFunctor(self._analytic_type, self._group, self._weight, self._ep), BaseFacade(self._base_ring)
        else:
            return FormsSubSpaceFunctor(self._analytic_type, self._group, self._weight, self._ep, self._basis), BaseFacade(self._base_ring)

    @cached_method
    def weight(self):
        r"""
        Return the weight of (elements of) ``self``.
        """

        return self._weight

    @cached_method
    def ep(self):
        r"""
        Return the multiplier of (elements of) ``self``.
        """

        return self._ep

    def element_from_coordinates(self, vec):
        r"""
        If ``self`` has an associated free module, then return the element of ``self``
        corresponding to the given coordinate vector ``vec``. Otherwise raise an exception.

        INPUT:

        - ``vec``     - A coordinate vector with respect to ``self.gens()``.

        OUTPUT:

        An element of ``self`` corresponding to the coordinate vector ``vec``.
        """

        if not self.module():
            raise Exception("No _module defined for {}".format(self))
        basis = self.gens()
        assert(len(basis) == len(vec))
        # vec = self.module()(self.module().linear_combination_of_basis(vec))
        # this also handles the trivial case (dimension 0)
        return self(sum([vec[k]*basis[k] for k in range(0, len(vec))]))

    def element_from_ambient_coordinates(self, vec):
        r"""
        If ``self`` has an associated free module, then return the element of ``self``
        corresponding to the given ``vec``. Otherwise raise an exception.

        INPUT:

        - ``vec``     - An element of ``self.module()`` or ``self.ambient_module()``.

        OUTPUT:

        An element of ``self`` corresponding to ``vec``.
        """

        return self(self.ambient_space().element_from_coordinates(vec))

    def homogeneous_space(self, k, ep):
        r"""
        Since ``self`` already is a homogeneous component return ``self``
        unless the degree differs in which case an Exception is raised.
        """

        if (k==self._weight and ep==self._ep):
            return self
        else:
            raise Exception("{} already is homogeneous with degree ({}, {}) != ({}, {})!".format(self, self._weight, self._ep, k, ep))

    def weight_parameters(self):
        r"""
        Check whether ``self`` has a valid weight and multiplier.
        If not then an exception is raised. Otherwise the two weight
        paramters corresponding for the weight and multiplier of ``self``
        are returned.

        The weight parameters are e.g. used to calculate dimensions
        or precisions of Fourier expansion.
        """

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
        r"""
        The automorphy factor of ``self``.

        For now it is only defined on the two basic generators of the
        Hecke group of ``self`` and their inverses.

        However, when determening the map which sends an element ``t``
        of the upper half plane to the fundamental domain, the
        function ``self.group().get_FD(t, self.aut_factor)`` can be used.
        It returns the full automorphy factor of the transformation matrix
        applied to ``t``.        

        INPUT:

        - ``gamma``   - An element of the group of ``self``. For now only
                        the basic generators (and their inverses) are supported.
        - ``t``       - An element of the upper half plane.
        """

        if (gamma == self._group.T or gamma == self._group.T.inverse()):
            return 1
        elif (gamma == self._group.S or gamma == -self._group.S):
            return self._ep*(t/AlgebraicField()(i))**self._weight
        else:
            raise NotImplementedError

    @cached_method
    def F_simple(self):
        r"""
        Return a (the most) simple normalized element of ``self`` corresponding to the weight
        parameters ``l1=self._l1`` and ``l2=self._l2``. If the element does not lie in
        ``self`` the type of its parent is extended accordingly.

        The main part of the element is given by a power (``l1``) of ``F_inf``, up to a small
        holomorphic correction factor.
        """

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

    def Faber_pol(self, m, fix_d=False, d_num_prec=None):
        r"""
        Return the ``m``'th Faber polynomial of ``self``.

        Namely a polynomial P(q) such that ``P(J_inv)*F_simple()``
        has a Fourier expansion of the form ``q^(-m) + O(q^(self._l1))``.
        ``d^(self._l1+m)*P(q)`` is a monic polynomial of degree ``self._l1 + m``.

        The Faber polynomials are used to construct a basis of weakly holomorphic forms
        and to recover such forms from their initial Fourier coefficients.

        INPUT:

        - ``m``            - An integer ``m >= -self._l1``.
        - ``fix_d``        - ``True`` if the value of ``d`` should be
                             (numerically) substituted for the coefficients
                             of the polynomial (default: ``False``).
        - ``d_num_prec``   - The numerical precision to be used for ``d``
                             in case ``fix_d`` is ``True``.
                             Default: ``None``, in which case the default
                             numerical precision ``self.num_prec()`` is used.

        OUTPUT:

        The corresponding Faber polynomial P(q) with coefficients in ``self.coeff_ring()``
        resp. a numerical ring in case ``fix_d`` is ``True``
        (and the group of ``self`` is not arithmetic).
        """

        m = ZZ(m)
        if (m < -self._l1):
            raise Exception("Invalid basis index: {}<{}!".format(m,-self._l1))
        if (d_num_prec == None):
            d_num_prec = self._num_prec

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

    # very similar to Faber_pol: faber_pol(q)=Faber_pol(d*q)
    def faber_pol(self, m, fix_d=False, d_num_prec=None):
        r"""
        Return the ``m``'th Faber polynomial of ``self``
        with a different normalization based on ``j_inv``
        instead of ``J_inv``.

        Namely a polynomial p(q) such that ``p(j_inv)*F_simple()``
        has a Fourier expansion of the form ``q^(-m) + O(q^(self._l1))``.
        ``p(q)`` is a monic polynomial of degree ``self._l1 + m``.

        The relation to ``Faber_pol`` is: ``faber_pol(q) = Faber_pol(d*q)``.

        INPUT:

        - ``m``            - An integer ``m >= -self._l1``.
        - ``fix_d``        - ``True`` if the value of ``d`` should be
                             (numerically) substituted for the coefficients
                             of the polynomial (default: ``False``).
        - ``d_num_prec``   - The numerical precision to be used for ``d``
                             in case ``fix_d`` is ``True``.
                             Default: ``None``, in which case the default
                             numerical precision ``self.num_prec()`` is used.

        OUTPUT:

        The corresponding Faber polynomial p(q) with coefficients in ``self.coeff_ring()``
        resp. a numerical ring in case ``fix_d`` is ``True``
        (and the group of ``self`` is not arithmetic).
        """

        m = ZZ(m)
        if (m < -self._l1):
            raise Exception("Invalid basis index: {}<{}!".format(m,-self._l1))
        if (d_num_prec == None):
            d_num_prec = self._num_prec

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
        r"""
        Returns a polynomial corresponding to the basis
        element of the correponding space of weakly holomorphic
        forms of the same degree as ``self``. The basis element
        is determined by the property that the Fourier expansion
        is of the form ``q^(-m) + O(q^(self._l1))``.

        INPUT:
        
        - ``m``            - An integer ``m >= -self._l1``.

        OUTPUT:

        A polynomial in ``x,y,z,d``, corresponding to ``F_rho, F_i, E2``
        and the (possibly) transcendental parameter ``d``.
        """

        (x,y,z,d) = self.rat_field().gens()

        n        = self._group.n
        finf_pol = d*(x**n-y**2)
        jinv_pol = x**n/(x**n-y**2)
        rat      = finf_pol**self._l1 * x**self._l2 * y**(ZZ(1-self._ep)/ZZ(2)) * self.Faber_pol(m)(jinv_pol)

        #return self(self.F_simple()*self.Faber_pol(m)(self.graded_ring().J_inv()))
        return rat

    def F_basis(self, m):
        r"""
        Returns a weakly holomorphic element of ``self``
        (extended if necessarily) determined by the property that
        the Fourier expansion is of the form is of the form
        ``q^(-m) + O(q^(self._l1))``.

        In particular for all ``m >= -self._l1`` these elements form
        a basis of the space of weakly holomorphic modular forms
        of the corresponding degree.

        INPUT:
        
        - ``m``            - An integer ``m >= -self._l1``.

        OUTPUT:

        The corresponding element in (possibly an extension of) ``self``.
        """

        if (m < 0):
            new_space = self.extend_type("cusp")
        elif (m == 0):
            new_space = self.extend_type("holo")
        else:
            new_space = self.extend_type("weak")

        return new_space(self.F_basis_pol(m))

    # TODO: This only works for weakly holomorphic modular forms!
    def construct_form(self, laurent_series):
        r"""
        Tries to construct an element of self with the given Fourier
        expansion. The assumption is made that the specified Fourier
        expansion corresponds to a weakly holomorphic modular form.

        If the precision is too low to determine the
        element an exception is raised.

        INPUT:

        - ``laurent_series``   - A Laurent or Power series.        

        OUTPUT:

        If possible: An element of self with the same initial
        Fourier expansion as ``laurent_series``.
        """

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
        r"""
        Return an element of ``self``.
        """

        # this seems ok, so might as well leave it as is for everything
        return self(ZZ(0))
        #return self.F_simple()

    @cached_method
    def dimension(self):
        r"""
        This method should be overloaded by subclasses.

        Return the dimension of ``self``.
        """

        return infinity
 
    def rank(self):
        r"""
        Return the rank of ``self``.
        """

        return self.dimension()

    def degree(self):
        r"""
        Return the degree of ``self``.
        """

        return self.dimension()
 
    def coordinate_vector(self, v):
        r"""
        This method should be overloaded by subclasses.

        Return the coordinate vector of the element ``v``
        with respect to ``self.gens()``.
        
        Note: Elements use this method (from their parent)
        to calculate their coordinates.
        """

        raise NotImplementedError

    @cached_method
    def ambient_coordinate_vector(self, v):
        r"""
        Return the coordinate vector of the element ``v``
        in ``self.module()`` with respect to the basis
        from ``self.ambient_space``.
        
        Note: Elements use this method (from their parent)
        to calculate their coordinates.
        """

        return self.module()(self.ambient_space().coordinate_vector(v))
 
    def gens(self):
        r"""
        This method should be overloaded by subclasses.

        Return a basis of ``self``.
        
        Note that the coordinate vector of elements of ``self``
        are with respect to this basis.
        """

        raise NotImplementedError
 
    def gen(self, k=0):
        r"""
        Return the ``k``'th basis element of ``self``
        if possible (default: ``k=0``).
        """

        k = ZZ(k)
        if k>=0 and k < self.dimension():
            return self.gens()[k]
        else:
            raise Exception("Invalid index: k={} does not satisfy 0 <= k <= {}!".format(k, self.dimension()))
