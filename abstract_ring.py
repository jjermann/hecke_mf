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
    from graded_ring_element import FormsRingElement
    Element = FormsRingElement

    from analytic_type import AnalyticType
    AT = AnalyticType()

    def __init__(self, group, base_ring, red_hom):
        r"""
        Abstract space for (Hecke) forms ring.

        INPUT:

        - ``group``       - The Hecke triangle group (default: ``HeckeTriangleGroup(3)``)
        - ``base_ring``   - The base_ring (default: ``ZZ``).
        - ``red_hom``     - If True then results of binary operations are considered
                            homogeneous whenever it makes sense (default: False).
                            This is mainly used by the Forms subclasses.

        OUTPUT:

        The corresponding abstract forms ring.
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
        self.set_default_disp_prec(5)
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
        from graded_ring_element import FormsRingElement
        if isinstance(x, FormsRingElement):
            x = self._rat_field(x._rat)
        else:
            x = self._rat_field(x)
        return self.element_class(self, x)

    def _coerce_map_from_(self, S):
        from space import FormsSpace_abstract
        if (    isinstance(S, FormsRing_abstract)\
            and self._group         == S._group\
            and self._analytic_type >= S._analytic_type\
            and self.base_ring().has_coerce_map_from(S.base_ring()) ):
                return True
        elif isinstance(S, FormsSpace_abstract):
            return self._coerce_map_from_(S.graded_ring())
        elif (self.AT("holo") <= self._analytic_type) and (self.coeff_ring().has_coerce_map_from(S)):
            return True
        else:
            return False

    def set_default_prec(self, prec = ZZ(10)):
        self._prec = ZZ(prec)
    def set_default_disp_prec(self, disp_prec = None):
        if (disp_prec == None):
            disp_prec = self._prec;
        self._disp_prec = ZZ(disp_prec)
    def set_default_num_prec(self, num_prec = ZZ(53)):
        self._num_prec = ZZ(num_prec)

    def _an_element_(self):
        return self(self.Delta())
    def change_ring(self, new_base_ring):
        return self.__class__.__base__(self._group, new_base_ring, self._red_hom)
    def graded_ring(self):
        return self.extend_type(ring=True)

    # This ensures that the new spaces contains elements with the listed attribute(s)
    def extend_type(self, analytic_type=None, ring=None):
        if analytic_type == None:
            analytic_type = self._analytic_type
        else:
            analytic_type = self._analytic_type.extend_by(analytic_type)

        if (ring or not self.is_homogeneous()):
            return FormsRing(analytic_type, group=self.group(), base_ring=self.base_ring(), red_hom=self.has_reduce_hom())
        else:
            return FormsSpace(analytic_type, group=self.group(), base_ring=self.base_ring(), k=self.weight(), ep=self.ep())

    # This ensures that all elements of the new spaces satisfy the listed attribute(s)
    def reduce_type(self, analytic_type=None, degree=None):
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

    # default implementation
    def construction(self):
        from functors import FormsRingFunctor, BaseFacade
        return FormsRingFunctor(self._analytic_type, self._group, self._red_hom), BaseFacade(self._base_ring)

    @cached_method
    def group(self):
        return self._group
    @cached_method
    def hecke_n(self):
        return self._group.n
    @cached_method
    def base_ring(self):
        return self._base_ring
    @cached_method
    def coeff_ring(self):
        return self._coeff_ring
    @cached_method
    def pol_ring(self):
        return self._pol_ring
    @cached_method
    def rat_field(self):
        return self._rat_field
    @cached_method
    def diff_alg(self):
        return self._diff_alg
    @cached_method
    def has_reduce_hom(self):
        return self._red_hom

    def is_homogeneous(self):
        return self._weight != None
    def is_modular(self):
        return not (self.AT("quasi") <= self._analytic_type)
    def is_weakly_holomorphic(self):
        return (self.AT("weak", "quasi") >= self._analytic_type)
    def is_holomorphic(self):
        return (self.AT("holo", "quasi") >= self._analytic_type)
    def is_cuspidal(self):
        return (self.AT("cusp", "quasi") >= self._analytic_type)
    def is_zerospace(self):
        return (self.AT(["quasi"]) >= self._analytic_type)
    def analytic_type(self):
        return self._analytic_type

    def homogeneous_space(self, k, ep):
        return self.reduce_type(degree = (k,ep))

    @cached_method
    def J_inv(self):
        (x,y,z,d) = self._pol_ring.gens()
        return self.extend_type("weak", ring=True)(x**self._group.n/(x**self._group.n-y**2)).reduce()
    # normalized by first Fourier coefficient
    # note that if J_inv is modified a lot of other functions have to be modified as well
    @cached_method
    def j_inv(self):
        (x,y,z,d) = self._pol_ring.gens()
        return self.extend_type("weak", ring=True)(1/d*x**self._group.n/(x**self._group.n-y**2)).reduce()
    @cached_method
    def F_rho(self):
        (x,y,z,d) = self._pol_ring.gens()
        return self.extend_type("holo", ring=True)(x).reduce()
    @cached_method
    def F_i(self):
        (x,y,z,d) = self._pol_ring.gens()
        return self.extend_type("holo", ring=True)(y).reduce()
    @cached_method
    def F_inf(self):
        (x,y,z,d) = self._pol_ring.gens()
        return self.extend_type("cusp", ring=True)(d*(x**self._group.n-y**2)).reduce()
    @cached_method
    def G_inv(self):
        if (ZZ(2).divides(self._group.n)):
            (x,y,z,d) = self._pol_ring.gens()
            return self.extend_type("weak", ring=True)(d*y*x**(self._group.n/ZZ(2))/(x**self._group.n-y**2)).reduce()
        else:
           raise Exception("G_inv doesn't exists for n={}.".format(self._group.n))
    # normalized by Fourier coefficient
    @cached_method
    def g_inv(self):
        if (ZZ(2).divides(self._group.n)):
            (x,y,z,d) = self._pol_ring.gens()
            return self.extend_type("weak", ring=True)(1/d*y*x**(self._group.n/ZZ(2))/(x**self._group.n-y**2)).reduce()
        else:
           raise Exception("g_inv doesn't exists for n={}.".format(self._group.n))
    @cached_method
    def E4(self):
        (x,y,z,d) = self._pol_ring.gens()
        return self.extend_type("holo", ring=True)(x**(self._group.n-2)).reduce()
    @cached_method
    def E6(self):
        (x,y,z,d) = self._pol_ring.gens()
        return self.extend_type("holo", ring=True)(x**(self._group.n-3)*y).reduce()
    @cached_method
    def Delta(self):
        (x,y,z,d) = self._pol_ring.gens()
        return self.extend_type("cusp", ring=True)(d*x**(2*self._group.n-6)*(x**self._group.n-y**2)).reduce()
    @cached_method
    def E2(self):
        (x,y,z,d) = self._pol_ring.gens()
        return self.extend_type(["holo", "quasi"], ring=True)(z).reduce()
