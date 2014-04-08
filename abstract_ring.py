r"""
Graded rings of modular forms for Hecke triangle groups

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

from sage.rings.all import FractionField, PolynomialRing, ZZ, QQ, infinity
from sage.algebras.free_algebra import FreeAlgebra

from sage.structure.parent import Parent
from sage.misc.cachefunc import cached_method

from hecke_triangle_groups import HeckeTriangleGroup
from constructor import FormsRing, FormsSpace, rational_type


# Maybe replace Parent by just SageObject?
class FormsRing_abstract(Parent):
    r"""
    Abstract (Hecke) forms ring.
    """

    from graded_ring_element import FormsRingElement
    Element = FormsRingElement

    from analytic_type import AnalyticType
    AT = AnalyticType()

    def __init__(self, group, base_ring, red_hom):
        r"""
        Abstract (Hecke) forms ring.

        INPUT:

        - ``group``       - The Hecke triangle group (default: ``HeckeTriangleGroup(3)``)
        - ``base_ring``   - The base_ring (default: ``ZZ``).
        - ``red_hom``     - If True then results of binary operations are considered
                            homogeneous whenever it makes sense (default: False).
                            This is mainly used by the (Hecke) forms.

        OUTPUT:

        The corresponding abstract (Hecke) forms ring.
        """

        from graded_ring import canonical_parameters
        (group, base_ring, red_hom) = canonical_parameters(group, base_ring, red_hom)

        if (group == infinity):
            raise NotImplementedError

        #if (not group.is_arithmetic() and base_ring.characteristic()>0):
        #    raise NotImplementedError
        #if (base_ring.characteristic().divides(2*group.n*(group.n-2))):
        #    raise NotImplementedError
        if (base_ring.characteristic() > 0):
            raise NotImplementedError
        self._group               = group
        self._red_hom             = red_hom
        self._base_ring           = base_ring
        self._coeff_ring          = FractionField(PolynomialRing(base_ring,'d'))
        self._pol_ring            = PolynomialRing(base_ring,'x,y,z,d')
        self._rat_field           = FractionField(self._pol_ring)

        # default values
        self._weight              = None
        self._ep                  = None
        self._analytic_type       = self.AT(["quasi", "mero"])

        self.set_default_prec()
        self.set_disp_prec(5)
        self.set_default_num_prec()

        # We only use two operators for now which do not involve 'd', so for performance
        # reason we choose FractionField(base_ring) instead of self.coeff_ring().
        self._free_alg            = FreeAlgebra(FractionField(ZZ),6,'X,Y,Z,dX,dY,dZ')
        (X,Y,Z,dX,dY,dZ)          = self._free_alg.gens()
        self._diff_alg            = self._free_alg.g_algebra({dX*X:1+X*dX,dY*Y:1+Y*dY,dZ*Z:1+Z*dZ})
        (X,Y,Z,dX,dY,dZ)          = self._diff_alg.gens()
        self._derivative_op       =   1/self._group.n * (X*Z-Y)*dX\
                                    + 1/2 * (Y*Z-X**(self._group.n-1))*dY\
                                    + (self._group.n-2) / (4*self._group.n) * (Z**2-X**(self._group.n-2))*dZ
        self._serre_derivative_op = - 1/self._group.n * Y*dX\
                                    - 1/2 * X**(self._group.n-1)*dY\
                                    - (self._group.n-2) / (4*self._group.n) * (Z**2-X**(self._group.n-2))*dZ

        #super(FormsRing_abstract, self).__init__(self.coeff_ring())

    def __cmp__(self, other):
        r"""
        Compare ``self`` and ``right``.
        """

        if (type(self)!=type(other)):
            return -1
        elif (self.group == other.group and self.base_ring == other.base_ring):
            return 0
        else:
            return -1

    def _repr_(self):
        r"""
        Return the string representation of ``self``.
        """

        return "{}FormsRing(n={}) over {}".format(self._analytic_type.analytic_space_name(), self._group.n, self._base_ring)

    def _latex_(self):
        r"""
        Return the LaTeX representation of ``self``.
        """

        from sage.misc.latex import latex
        return "\\mathcal{{ {} }}_{{n={}}}({})".format(self._analytic_type.latex_space_name(), self._group.n, latex(self._base_ring))

    def _element_constructor_(self, x):
        r"""
        Return ``x`` coerced/converted into this forms ring.
        """

        from graded_ring_element import FormsRingElement
        if isinstance(x, FormsRingElement):
            x = self._rat_field(x._rat)
        else:
            x = self._rat_field(x)
        return self.element_class(self, x)

    def _coerce_map_from_(self, S):
        r"""
        Return whether or not there exists a coercion from ``S`` to ``self``.
        """

        from space import FormsSpace_abstract
        if (    isinstance(S, FormsRing_abstract)\
            and self._group         == S._group\
            and self._analytic_type >= S._analytic_type\
            and self.base_ring().has_coerce_map_from(S.base_ring()) ):
                return True
        # TODO: This case never occurs: remove it?
        elif isinstance(S, FormsSpace_abstract):
            return self._coerce_map_from_(S.graded_ring())
        elif (self.AT("holo") <= self._analytic_type) and (self.coeff_ring().has_coerce_map_from(S)):
            return True
        else:
            return False

    def set_default_prec(self, prec = ZZ(10)):
        r"""
        Set the default precision ``prec`` for the Fourier expansion (default: ``10``).
        Note that this is also used as the default precision for the Fourier expansion 
        when evaluating forms.
        """

        self._prec = ZZ(prec)
    
    def default_prec(self):
        r"""
        Returns the default precision for the Fourier expansion of ``self``.
        """

        return self._prec

    def set_disp_prec(self, disp_prec = None):
        r"""
        Set the maximal precision ``disp_prec`` used for displaying (elements of) ``self``
        as a Fourier expansion. If ``disp_prec`` is ``None`` (default) then the
        default precision is used.
        """

        if (disp_prec == None):
            disp_prec = self._prec;
        self._disp_prec = ZZ(disp_prec)

    def default_disp_prec(self):
        r"""
        Returns the default display precision for Fourier expansion representations
        of (elements of) ``self``.
        """

        return self._disp_prec

    def set_default_num_prec(self, num_prec = ZZ(53)):
        r"""
        Set the default numerical precision ``num_prec`` (default: ``53``).
        """

        self._num_prec = ZZ(num_prec)

    def default_num_prec(self):
        r"""
        Returns the default numerical precision of ``self``.
        """

        return self._disp_prec

    def _an_element_(self):
        r"""
        Return an element of ``self``.
        """

        return self(self.Delta())

    def change_ring(self, new_base_ring):
        r"""
        Return the same space as ``self`` but over a new base ring ``new_base_ring``.
        """

        return self.__class__.__base__(self._group, new_base_ring, self._red_hom)

    def graded_ring(self):
        r"""
        Return the graded ring containing ``self``.
        """

        return self.extend_type(ring=True)

    def extend_type(self, analytic_type=None, ring=False):
        r"""
        Return a new space which contains (elements of) ``self`` with the analytic type
        of ``self`` extended by ``analytic_type``, possibly extended to a graded ring
        in case ``ring`` is ``True``.
        
        INPUT:
        
        - ``analytic_type``   - An ``AnalyticType`` or something which coerces into it (default: ``None``).
        - ``ring``            - Whether to extend to a graded ring (default: ``False``).

        OUTPUT:
        
        The new extended space.        
        """

        if analytic_type == None:
            analytic_type = self._analytic_type
        else:
            analytic_type = self._analytic_type.extend_by(analytic_type)

        if (ring or not self.is_homogeneous()):
            return FormsRing(analytic_type, group=self.group(), base_ring=self.base_ring(), red_hom=self.has_reduce_hom())
        else:
            return FormsSpace(analytic_type, group=self.group(), base_ring=self.base_ring(), k=self.weight(), ep=self.ep())

    def reduce_type(self, analytic_type=None, degree=None):
        r"""
        Return a new space with analytic properties shared by both ``self`` and ``analytic_type``,
        possibly reduced to its homogeneous space of the given ``degree`` (if ``degree`` is set).
        Elements of the new space are contained in ``self``.
        
        INPUT:
        
        - ``analytic_type``   - An ``AnalyticType`` or something which coerces into it (default: ``None``).
        - ``degree``          - ``None`` (default) or the degree of the homogeneous component to which
                                ``self`` should be reduced.

        OUTPUT:
        
        The new reduced space.
        """

        if analytic_type == None:
            analytic_type = self._analytic_type
        else:
            analytic_type = self._analytic_type.reduce_to(analytic_type)

        if (degree == None and not self.is_homogeneous()):
            return FormsRing(analytic_type, group=self.group(), base_ring=self.base_ring(), red_hom=self.has_reduce_hom())
        elif (degree == None):
            return FormsSpace(analytic_type, group=self.group(), base_ring=self.base_ring(), k=self.weight(), ep=self.ep())
        else:
            (weight, ep) = degree
            if (self.is_homogeneous() and (weight != self.weight() or ep!=self.ep())):
                analytic_type = self._analytic_type.reduce_to([])
            return FormsSpace(analytic_type, group=self.group(), base_ring=self.base_ring(), k=weight, ep=ep)

    def construction(self):
        r"""
        Return a functor that constructs ``self`` (used by the coercion machinery).

        EXAMPLE:: 

        sage: from graded_ring import ModularFormsRing
        sage: ModularFormsRing().construction()
        (ModularFormsRingFunctor(n=3), BaseFacade(Integer Ring))
        """

        from functors import FormsRingFunctor, BaseFacade
        return FormsRingFunctor(self._analytic_type, self._group, self._red_hom), BaseFacade(self._base_ring)

    @cached_method
    def group(self):
        r"""
        Return the (Hecke triangle) group of ``self``.
        """

        return self._group

    @cached_method
    def hecke_n(self):
        r"""
        Return the parameter ``n`` of the
        (Hecke triangle) group of ``self``.
        """

        return self._group.n

    @cached_method
    def base_ring(self):
        r"""
        Return base ring of ``self``.
        """

        return self._base_ring

    @cached_method
    def coeff_ring(self):
        r"""
        Return coefficient ring of ``self``.
        """

        return self._coeff_ring

    @cached_method
    def pol_ring(self):
        r"""
        Return the underlying polynomial ring used
        by ``self``.
        """

        return self._pol_ring

    @cached_method
    def rat_field(self):
        r"""
        Return the underlying rational field used by
        ``self`` to construct/represent elements.
        """

        return self._rat_field

    @cached_method
    def diff_alg(self):
        r"""
        Return the algebra of differential operators
        (over QQ) which is used on rational functions
        representing elements of ``self``.
        """

        return self._diff_alg

    @cached_method
    def has_reduce_hom(self):
        r"""
        Return whether the method ``reduce`` should reduce
        homogeneous elements to the corresponding homogeneous space.

        This is mainly used by binary operations on homogeneous
        spaces which temporarily produce an element of ``self``
        but want to consider it as a homogeneous element
        (also see ``reduce``).
        """

        return self._red_hom

    def is_homogeneous(self):
        r"""
        Return whether ``self`` is homogeneous component.
        """

        return self._weight != None

    def is_modular(self):
        r"""
        Return whether ``self`` only contains modular elements.
        """

        return not (self.AT("quasi") <= self._analytic_type)

    def is_weakly_holomorphic(self):
        r"""
        Return whether ``self`` only contains weakly
        holomorphic modular elements.
        """

        return (self.AT("weak", "quasi") >= self._analytic_type)

    def is_holomorphic(self):
        r"""
        Return whether ``self`` only contains holomorphic
        modular elements.
        """

        return (self.AT("holo", "quasi") >= self._analytic_type)

    def is_cuspidal(self):
        r"""
        Return whether ``self`` only contains cuspidal elements.
        """

        return (self.AT("cusp", "quasi") >= self._analytic_type)

    def is_zerospace(self):
        r"""
        Return whether ``self`` is the (0-dimensional) zero space.
        """

        return (self.AT(["quasi"]) >= self._analytic_type)

    def analytic_type(self):
        r"""
        Return the analytic type of ``self``.
        """

        return self._analytic_type

    def homogeneous_space(self, k, ep):
        r"""
        Return the homogeneous component of degree (``k``, ``e``) of ``self``.
        """

        return self.reduce_type(degree = (k,ep))

    @cached_method
    def J_inv(self):
        r"""
        Return the J-invariant (Hauptmodul) of the group of ``self``.
        It is normalized such that ``J_inv(infinity) = infinity``,
        it has real Fourier coefficients starting with ``d > 0`` and ``J_inv(i) = 1``

        It lies in a (weak) extension of the graded ring of ``self``.
        In case ``has_reduce_hom`` is ``True`` it is given as an element of
        the corresponding homogeneous space.
        """

        (x,y,z,d) = self._pol_ring.gens()
        return self.extend_type("weak", ring=True)(x**self._group.n/(x**self._group.n-y**2)).reduce()

    @cached_method
    def j_inv(self):
        r"""
        Return the j-invariant (Hauptmodul) of the group of ``self``.
        It is normalized such that ``j_inv(infinity) = infinity``,
        and such that it has real Fourier coefficients starting with ``1``.

        It lies in a (weak) extension of the graded ring of ``self``.
        In case ``has_reduce_hom`` is ``True`` it is given as an element of
        the corresponding homogeneous space.
        """

        (x,y,z,d) = self._pol_ring.gens()
        return self.extend_type("weak", ring=True)(1/d*x**self._group.n/(x**self._group.n-y**2)).reduce()

    @cached_method
    def F_rho(self):
        r"""
        Return the generator ``F_rho`` of the graded ring of ``self``.
        Up to the group action ``F_rho`` has exactly one simple zero at ``rho``. ``F_rho`` is
        normalized such that its first nontrivial Fourier coefficient is ``1``.

        The polynomial variable ``x`` exactly corresponds to ``F_rho``.

        It lies in a (cuspidal) extension of the graded ring of ``self``.
        In case ``has_reduce_hom`` is ``True`` it is given as an element of
        the corresponding homogeneous space.
        """

        (x,y,z,d) = self._pol_ring.gens()
        return self.extend_type("holo", ring=True)(x).reduce()

    @cached_method
    def F_i(self):
        r"""
        Return the generator ``F_i`` of the graded ring of ``self``.
        Up to the group action ``F_i`` has exactly one simple zero at ``i``. ``F_i`` is
        normalized such that its first nontrivial Fourier coefficient is ``1``.
        
        The polynomial variable ``y`` exactly corresponds to ``F_i``.

        It lies in a (holomorphic) extension of the graded ring of ``self``.
        In case ``has_reduce_hom`` is ``True`` it is given as an element of
        the corresponding homogeneous space.
        """

        (x,y,z,d) = self._pol_ring.gens()
        return self.extend_type("holo", ring=True)(y).reduce()

    @cached_method
    def F_inf(self):
        r"""
        Return the first nontrivial cusp form ``F_inf`` of the graded ring of ``self``.
        Up to the group action ``F_inf`` has exactly one simple zero at ``infinity``.
        ``F_inf`` is normalized such that its first nontrivial Fourier coefficient is ``1``.

        It lies in a (holomorphic) extension of the graded ring of ``self``.
        In case ``has_reduce_hom`` is ``True`` it is given as an element of
        the corresponding homogeneous space.
        """

        (x,y,z,d) = self._pol_ring.gens()
        return self.extend_type("cusp", ring=True)(d*(x**self._group.n-y**2)).reduce()

    @cached_method
    def G_inv(self):
        r"""
        If ``2`` divides ``n``: Return the G-invariant of the group of ``self``.
        
        The G-invariant is analogous to the G-invariant but has multiplier ``-1``.
        I.e. ``G_inv(-1/t) = -G_inv(t)``. It is a holomorphic square root
        of ``J_inv*(J_inv-1)`` with real Fourier coefficients.
        
        If ``2`` does not divide ``n`` the function doesn't exist and an exception is raised.

        It lies in a (weak) extension of the graded ring of ``self``.
        In case ``has_reduce_hom`` is ``True`` it is given as an element of
        the corresponding homogeneous space.
        """

        if (ZZ(2).divides(self._group.n)):
            (x,y,z,d) = self._pol_ring.gens()
            return self.extend_type("weak", ring=True)(d*y*x**(self._group.n/ZZ(2))/(x**self._group.n-y**2)).reduce()
        else:
           raise Exception("G_inv doesn't exists for n={}.".format(self._group.n))

    @cached_method
    def g_inv(self):
        r"""
        If ``2`` divides ``n``: Return the g-invariant of the group of ``self``.
        
        The g-invariant is analogous to the j-invariant but has multiplier ``-1``.
        I.e. ``g_inv(-1/t) = -g_inv(t)``. It is a (normalized) holomorphic square root
        of ``J_inv*(J_inv-1)``, normalized such that its first nontrivial Fourier coefficient is ``1``.
        
        If ``2`` does not divide ``n`` the function doesn't exist and an exception is raised.

        It lies in a (weak) extension of the graded ring of ``self``.
        In case ``has_reduce_hom`` is ``True`` it is given as an element of
        the corresponding homogeneous space.
        """

        if (ZZ(2).divides(self._group.n)):
            (x,y,z,d) = self._pol_ring.gens()
            return self.extend_type("weak", ring=True)(1/d*y*x**(self._group.n/ZZ(2))/(x**self._group.n-y**2)).reduce()
        else:
           raise Exception("g_inv doesn't exists for n={}.".format(self._group.n))

    @cached_method
    def E4(self):
        r"""
        Return the normalized Eisenstein series of weight ``4`` of the graded ring of ``self``.
        It is equal to ``F_rho^(n-2)``.

        It lies in a (holomorphic) extension of the graded ring of ``self``.
        In case ``has_reduce_hom`` is ``True`` it is given as an element of
        the corresponding homogeneous space.
        """

        (x,y,z,d) = self._pol_ring.gens()
        return self.extend_type("holo", ring=True)(x**(self._group.n-2)).reduce()

    @cached_method
    def E6(self):
        r"""
        Return the normalized Eisenstein series of weight ``6`` of the graded ring of ``self``,
        It is equal to ``F_rho^(n-3) * F_i``.

        It lies in a (holomorphic) extension of the graded ring of ``self``.
        In case ``has_reduce_hom`` is ``True`` it is given as an element of
        the corresponding homogeneous space.
        """

        (x,y,z,d) = self._pol_ring.gens()
        return self.extend_type("holo", ring=True)(x**(self._group.n-3)*y).reduce()

    @cached_method
    def Delta(self):
        r"""
        Return an analog of the Delta-function of the graded ring of ``self``.
        It is a cusp form of weight ``12`` and is equal to
        ``d*(E4^3 - E6^2)`` or (in terms of the generators) ``d*x^(2*n-6)*(x^n - y^2)``.

        It lies in a (cuspidal) extension of the graded ring of ``self``.
        In case ``has_reduce_hom`` is ``True`` it is given as an element of
        the corresponding homogeneous space.
        """

        (x,y,z,d) = self._pol_ring.gens()
        return self.extend_type("cusp", ring=True)(d*x**(2*self._group.n-6)*(x**self._group.n-y**2)).reduce()

    @cached_method
    def E2(self):
        r"""
        Return the normalized quasi holomorphic Eisenstein series of weight ``2`` of the
        graded ring of ``self``. It is also a generator of the graded ring of
        ``self`` and  the polynomial variable ``z`` exactly corresponds to ``E2``.

        It lies in a (quasi holomorphic) extension of the graded ring of ``self``.
        In case ``has_reduce_hom`` is ``True`` it is given as an element of
        the corresponding homogeneous space.
        """

        (x,y,z,d) = self._pol_ring.gens()
        return self.extend_type(["holo", "quasi"], ring=True)(z).reduce()
