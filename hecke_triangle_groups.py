r"""
Hecke triangle groups

AUTHORS:

- Jonas Jermann (2013): initial version

"""

#*****************************************************************************
#       Copyright (C) 2013-2014 Jonas Jermann <jjermann2@gmail.com>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#  as published by the Free Software Foundation; either version 2 of
#  the License, or (at your option) any later version.
#                  http://www.gnu.org/licenses/
#*****************************************************************************

from sage.rings.all import ZZ, QQ, AA, AlgebraicField, infinity
from sage.functions.all import cos,exp,sec
from sage.functions.other import psi1
from sage.symbolic.all import pi,i
from sage.matrix.constructor import matrix
from sage.misc.latex import latex

from sage.groups.matrix_gps.finitely_generated import FinitelyGeneratedMatrixGroup_generic
from sage.structure.unique_representation import UniqueRepresentation
from sage.misc.cachefunc import cached_method

# This is just a stub implementation, to implement the class
# properly an element class has to be introduced/etc...

#from sage.matrix.matrix_space import MatrixSpace
#from sage.matrix.matrix_generic_dense import Matrix_generic_dense
#from hecke_triangle_group_element import *
#
#class HeckeTriangleGroup(MatrixSpace):
#    Element=HeckeTriangleGroupElement
#
#    @staticmethod
#    def __classcall__(self,n):
#        return super(MatrixSpace,self).__classcall__(self,n)
#
#    def __init__(self):
#        ...
#        self.element_class       = HeckeTriangleGroupElement
#        MatrixSpace.__init__(self,AA,ZZ(2))
#
#    def _get_matrix_class(self):
#        return Matrix_generic_dense
#        return HeckeTriangleGroupElement
# "act" should be implemented by HeckeTriangleGroupElement instead,
# using _l_action(self,t).


class HeckeTriangleGroup(FinitelyGeneratedMatrixGroup_generic, UniqueRepresentation):
    r"""
    Hecke triangle group (2, n, infinity).

    This is a stub implementation.
    """

    @staticmethod
    def __classcall__(cls, n=3):
        r"""
        Return a (cached) instance with canonical parameters.

        EXAMPLES::

            sage: HeckeTriangleGroup(QQ(3)) == HeckeTriangleGroup(int(3))
            True
        """

        if (n == infinity):
            n = infinity
        else:
            n = ZZ(n)
            if (n < 3):
                raise AttributeError("n has to be infinity or an Integer >= 3.")

        return super(HeckeTriangleGroup, cls).__classcall__(cls, n)

    def __init__(self, n):
        r"""
        Hecke triangle group (2, n, infinity).
        Namely the von Dyck group corresponding to the triangle group
        with angles (pi/2, pi/n, 0).

        INPUT:

        - ``n``   - ``infinity`` or an integer greater or equal to ``3``.

        OUTPUT:

        The Hecke triangle group for the given parameter ``n``.

        EXAMPLES::

            sage: G = HeckeTriangleGroup(12)
            sage: G
            Hecke triangle group for n = 12
            sage: G.category()
            Category of groups
        """

        self._n = n
        self._T = matrix(AA, [[1,self.lam()],[0,1]])
        self._S = matrix(AA, [[0,-1],[1,0]])

        FinitelyGeneratedMatrixGroup_generic.__init__(self, ZZ(2), AA, [self._S, self._T])

    @cached_method
    def n(self):
        r"""
        Return the parameter ``n`` of ``self``, where
        ``pi/n`` is the angle at ``rho`` of the corresponding
        basic hyperbolic triangle with vertices ``i``, ``rho``
        and ``infinity``.

        EXAMPLES::

            sage: HeckeTriangleGroup(10).n()
            10
            sage: HeckeTriangleGroup(infinity).n()
            +Infinity
        """

        return self._n

    @cached_method
    def lam(self):
        r"""
        Return the parameter ``lambda`` of ``self``,
        where ``lambda`` is twice the real part of ``rho``,
        lying between ``1`` (when ``n=3``) and ``2`` (when ``n=infinity``).

        EXAMPLES::

            sage: HeckeTriangleGroup(3).lam()
            1
            sage: HeckeTriangleGroup(4).lam()^2
            2.000000000000000?
            sage: HeckeTriangleGroup(6).lam()^2
            3.000000000000000?
            sage: HeckeTriangleGroup(10).lam()
            1.902113032590308?
        """

        return AA(2 * cos(pi/self._n))

    @cached_method
    def rho(self):
        r"""
        Return the vertex ``rho`` of the basic hyperbolic
        triangle which describes ``self``. ``rho`` has
        absolute value 1 and angle ``pi/n``.

        EXAMPLES::

            sage: HeckeTriangleGroup(3).rho() == 1/2 + sqrt(3)/2*i
            True
            sage: HeckeTriangleGroup(4).rho() == sqrt(2)/2*(1 + i)
            True
            sage: HeckeTriangleGroup(6).rho() == sqrt(3)/2 + 1/2*i
            True
            sage: HeckeTriangleGroup(10).rho()
            0.9510565162951536? + 0.3090169943749474?*I
                        
        """

        return AlgebraicField()(exp(pi/self._n*i))

    @cached_method
    def alpha(self):
        r"""
        Return the parameter ``alpha`` of ``self``.
        It is used in the calculation of the Hauptmodul of ``self``.

        EXAMPLES::

        sage: HeckeTriangleGroup(3).alpha()
        1/12
        sage: HeckeTriangleGroup(4).alpha()
        1/8
        sage: HeckeTriangleGroup(5).alpha()
        3/20
        sage: HeckeTriangleGroup(6).alpha()
        1/6
        sage: HeckeTriangleGroup(10).alpha()
        1/5
        """

        return ZZ(1)/ZZ(2) * (ZZ(1)/ZZ(2) - ZZ(1)/self._n)

    @cached_method
    def beta(self):
        r"""
        Return the parameter ``beta`` of ``self``.
        It is used in the calculation of the Hauptmodul of ``self``.

        EXAMPLES::

        sage: HeckeTriangleGroup(3).beta()
        5/12
        sage: HeckeTriangleGroup(4).beta()
        3/8
        sage: HeckeTriangleGroup(5).beta()
        7/20
        sage: HeckeTriangleGroup(6).beta()
        1/3
        sage: HeckeTriangleGroup(10).beta()
        3/10
        """

        return ZZ(1)/ZZ(2) * (ZZ(1)/ZZ(2) + ZZ(1)/self._n)

    @cached_method
    def I(self):
        r"""
        Return the identity element/matrix for ``self``.

        EXAMPLES::

            sage: HeckeTriangleGroup(10).I()
            [1 0]
            [0 1]
            sage: HeckeTriangleGroup(10).I().parent()  # todo: this should return self...
            Full MatrixSpace of 2 by 2 dense matrices over Algebraic Real Field
        """

        return matrix(AA, [[1,0],[0,1]])

    def one_element(self):
        r"""
        Return the identity element/matrix for ``self``.

        EXAMPLES::

            sage: HeckeTriangleGroup(10).one_element()
            [1 0]
            [0 1]
            sage: HeckeTriangleGroup(10).one_element().parent()  # todo: this should return self...
            Full MatrixSpace of 2 by 2 dense matrices over Algebraic Real Field
        """

        return self.I()

    @cached_method
    def T(self):
        r"""
        Return the generator of ``self`` corresponding to the translation
        by ``self.lam()``.

        EXAMPLES::

            sage: HeckeTriangleGroup(3).T()
            [1 1]
            [0 1]
            sage: HeckeTriangleGroup(10).T()
            [                 1 1.902113032590308?]
            [                 0                  1]
            sage: HeckeTriangleGroup(10).T().parent()  # todo: this should return self...
            Full MatrixSpace of 2 by 2 dense matrices over Algebraic Real Field
        """

        return self._T

    @cached_method
    def S(self):
        r"""
        Return the generator of ``self`` corresponding to the
        conformal circle inversion.

        EXAMPLES::

            sage: HeckeTriangleGroup(3).S()
            [ 0 -1]
            [ 1  0]
            sage: HeckeTriangleGroup(10).S()
            [ 0 -1]
            [ 1  0]
            sage: HeckeTriangleGroup(10).S()^2 == -HeckeTriangleGroup(10).I()
            True
            sage: HeckeTriangleGroup(10).S()^4 == HeckeTriangleGroup(10).I()
            True
            sage: HeckeTriangleGroup(10).S().parent()  # todo: this should return self...
            Full MatrixSpace of 2 by 2 dense matrices over Algebraic Real Field
        """

        return self._S

    @cached_method
    def U(self):
        r"""
        Return an alternative generator of ``self`` instead of ``T``.
        ``U`` stabilizes ``rho`` and has order ``2*self.n()``.

        EXAMPLES::

            sage: HeckeTriangleGroup(3).U()
            [ 1 -1]
            [ 1  0]
            sage: HeckeTriangleGroup(3).U()^3 == -HeckeTriangleGroup(3).I()
            True
            sage: HeckeTriangleGroup(3).U()^6 == HeckeTriangleGroup(3).I()
            True
            sage: HeckeTriangleGroup(10).U()
            [1.902113032590308?                 -1]
            [                 1                  0]
            sage: HeckeTriangleGroup(10).U()^10 == -HeckeTriangleGroup(10).I()
            True
            sage: HeckeTriangleGroup(10).U()^20 == HeckeTriangleGroup(10).I()
            True
            sage: HeckeTriangleGroup(10).U().parent()  # todo: this should return self...
            Full MatrixSpace of 2 by 2 dense matrices over Algebraic Real Field
        """

        return self._T * self._S

    def V(self, j):
        r"""
        Return the j'th generator for the usual representatives of
        conjugacy classes of ``self``. It is given by ``V=U^(j-1)*T``.
        
        INPUT:
        
        - ``j``  -- Any integer. To get the usual representatives
                    ``j`` should range from ``1`` to ``self.n()-1``.

        OUTPUT:
        
        The corresponding matrix/element.
        The matrix is parabolic if ``j`` is congruent to +-1 modulo ``self.n()``.
        It is elliptic if ``j`` is congruent to 0 modulo ``self.n()``.
        It is hyperbolic otherwise.

        EXAMPLES::

            sage: G = HeckeTriangleGroup(3)
            sage: G.V(0) == -G.S()
            True
            sage: G.V(1) == G.T()
            True
            sage: G.V(2)
            [1 0]
            [1 1]
            sage: G.V(3) == G.S()
            True

            sage: G = HeckeTriangleGroup(5)
            sage: G.V(1)
            [                 1 1.618033988749895?]
            [                 0                  1]
            sage: G.V(2)
            [1.618033988749895? 1.618033988749895?]
            [                 1 1.618033988749895?]
            sage: G.V(3)
            [1.618033988749895? 1.000000000000000?]
            [1.618033988749895? 1.618033988749895?]
            sage: G.V(4)
            [1.000000000000000?            0.?e-17]
            [1.618033988749895? 1.000000000000000?]
            sage: G.V(5) == G.S()
            True
        """

        return self.U()**(j-1) * self._T

    #TODO: Be more precise (transfinite diameter of what exactly)
    #TODO: Is d or 1/d the transfinite diameter?
    @cached_method
    def dvalue(self):
        r"""
        Return a symbolic expression (or an exact value in case n=3, 4, 6)
        for the transfinite diameter (or capacity) of ``self``.

        EXAMPLES:

            sage: HeckeTriangleGroup(3).dvalue()
            1/1728
            sage: HeckeTriangleGroup(4).dvalue()
            1/256
            sage: HeckeTriangleGroup(5).dvalue()
            e^(2*euler_gamma - 4*pi/(sqrt(5) + 1) + psi(17/20) + psi(13/20))
            sage: HeckeTriangleGroup(6).dvalue()
            1/108
            sage: HeckeTriangleGroup(10).dvalue()
            e^(2*euler_gamma - pi*sec(1/10*pi) + psi(4/5) + psi(7/10))
            sage: HeckeTriangleGroup(infinity).dvalue()
            1/64
        """

        n=self._n
        if (n==3):
            return ZZ(1)/ZZ(2**6*3**3)
        elif (n==4):
            return ZZ(1)/ZZ(2**8)
        elif (n==6):
            return ZZ(1)/ZZ(2**2*3**3)
        elif (n==infinity):
            return ZZ(1)/ZZ(2**6)
        else:
            return exp(-ZZ(2)*psi1(ZZ(1)) + psi1(ZZ(1)-self.alpha())+psi1(ZZ(1)-self.beta()) - pi*sec(pi/self._n))

    def _repr_(self):
        r"""
        Return the string representation of ``self``.

        EXAMPLES::

            sage: HeckeTriangleGroup(10)
            Hecke triangle group for n = 10
        """

        return "Hecke triangle group for n = {}".format(self._n)

    def _latex_(self):
        r"""
        Return the LaTeX representation of ``self``.

        EXAMPLES::

            sage: a = HeckeTriangleGroup(5)
            sage: latex(a)
            \Gamma^{(5)}
        """

        return '\\Gamma^{(%s)}'%(latex(self._n))

    def is_arithmetic(self):
        r"""
        Return True if ``self`` is an arithmetic subgroup.

        EXAMPLES:

            sage: HeckeTriangleGroup(3).is_arithmetic()
            True
            sage: HeckeTriangleGroup(4).is_arithmetic()
            True
            sage: HeckeTriangleGroup(5).is_arithmetic()
            False
            sage: HeckeTriangleGroup(6).is_arithmetic()
            True
            sage: HeckeTriangleGroup(10).is_arithmetic()
            False
            sage: HeckeTriangleGroup(infinity).is_arithmetic()
            True
        """

        if (self._n in [ZZ(3), ZZ(4), ZZ(6), infinity]):
            return True
        else:
            return False

    def act(self,mat,t):
        r"""
        Return the image of ``t`` under the action of the matrix ``mat``
        by linear fractional transformations.

        INPUT:

        - ``mat`` -- An element of the Hecke triangle group (no check is performed
          though and the function works for more general matrices as well).

        - ``t`` -- A complex number or an element of AlgebraicField().

        EXAMPLES::

            sage: G = HeckeTriangleGroup(5)
            sage: G.act(G.S(), AlgebraicField()(1 + i/2))
            2/5*I - 4/5
        """

        return (mat[0][0]*t + mat[0][1])/(mat[1][0]*t + mat[1][1])

    def get_FD(self, z, aut_factor=None):
        r"""
        Return a tuple (A,w,fact) which determines how to map ``z``
        to the usual (strict) fundamental domain of ``self``.

        INPUT:

        - ``z`` -- a complex number or an element of AlgebraicField().

        - ``aut_factor`` -- ``None`` (default) or an automorphy factor.
            The automorphy factor is a function ``aut_factor(mat, t)``.

            ``aut_factor`` only has to be defined for ``mat`` beeing
            one of two generators ``mat=self.T()``, `mat=self.S()`` or their
            inverses. See the remarks below as well.

            ``aut_factor`` has to be defined for ``t`` a complex number
            or ``t``an element of AlgebraicField().

        OUTPUT:

        A tuple (A,w,fact).

        - ``A`` -- a matrix in ``self`` such that ``self.act(A,w)==z``
          (if ``z`` is exact at least).

        - ``w`` -- a complex number or an element of AlgebraicField()
          (depending on the type ``z``) which lies inside the (strict)
          fundamental domain of ``self`` (``self.in_FD(w)==True``) and
          which is equivalent to ``z`` (by the above property).

        - ``factor`` -- ``1`` (if ``aut_factor==None``) or the automorphy
          factor evaluated on ``A`` and ``w`` (``"aut_factor(A,w)"``).

          An automorphy factor is a function ``factor(mat,t)`` with the property:
          ``factor(A*B,t)==factor(A,self.act(B,t))*factor(B,t)``.

          From this property the function is already determined by its
          definition on the generators. This function determines
          ``aut_factor(A,w)`` by using the definition on the generators and
          by applying the above properties.

          The function is for example used to determine the value of a
          modular form for Hecke triangle groups by its value ``w`` in
          the fundamental domain.

        EXAMPLES::

            sage: G = HeckeTriangleGroup(8)
            sage: z = AlgebraicField()(1+i/2)
            sage: (A,w,fact) = G.get_FD(z)
            sage: A
            [-1.847759065022574?                   1]
            [-1.000000000000000?                   0]
            sage: G.act(A,w) == z
            True
            sage: full_factor = lambda mat, t: (mat[1][0]*t+mat[1][1])**4
            sage: def aut_factor(mat,t):
            ....:     if (mat == G.T() or mat == G.T().inverse()):
            ....:         return 1
            ....:     elif (mat == G.S() or mat == G.S().inverse()):
            ....:         return t**4
            ....:     else:
            ....:         raise NotImplementedError
            sage: (A,w,fact) = G.get_FD(z,aut_factor)
            sage: fact == full_factor(A,w)
            True
        """

        I  = self.I()
        T  = self._T
        S  = self._S
        TI = self._T.inverse()

        A = I
        L = []
        w = z
        while (abs(w) < ZZ(1) or abs(w.real()) > self.lam()/ZZ(2)):
            if (abs(w) < ZZ(1)):
                w = self.act(self._S, w)
                A = S*A
                L.append(-S)
            if (w.real() >= self.lam()/ZZ(2)):
                w = self.act(TI, w)
                A = TI*A
                L.append(T)
            elif (w.real() < self.lam()/ZZ(2)):
                w = self.act(T, w)
                A = T*A
                L.append(TI)
        if (w.real() == self.lam()/ZZ(2)):
            w = self.act(TI, w)
            A = TI*A
            L.append(T)
        if (abs(w) == ZZ(1) and w.real() > ZZ(0)):
            w = self.act(S,w)
            A = S*A
            L.append(-S)

        if (aut_factor == None):
            new_factor = ZZ(1)
        else:
            B = I
            temp_w = self.act(A, z)
            new_factor = ZZ(1)
            for gamma in reversed(L):
                B = gamma*B
                new_factor *= aut_factor(gamma, temp_w)
                temp_w = self.act(gamma, temp_w)

        return (A.inverse(), self.act(A,z), new_factor)

    def in_FD(self,z):
        r"""
        Returns ``True`` if ``z`` lies in the (strict) fundamental
        domain of ``self``.

        EXAMPLES::

            sage: HeckeTriangleGroup(5).in_FD(CC(1.5/2 + 0.9*i))
            True
            sage: HeckeTriangleGroup(4).in_FD(CC(1.5/2 + 0.9*i))
            False
        """

        return self.get_FD(z)[0] == self.I()
