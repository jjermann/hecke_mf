r"""
Hecke triangle groups

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

from sage.rings.all import ZZ, QQ, AA, AlgebraicField, infinity
from sage.functions.all import cos,exp,sec
from sage.functions.other import psi1
from sage.symbolic.all import pi,i
from sage.matrix.constructor import matrix
from sage.misc.latex import latex
#from sage.matrix.matrix_space import MatrixSpace
#from sage.matrix.matrix_generic_dense import Matrix_generic_dense

from sage.groups.matrix_gps.finitely_generated import FinitelyGeneratedMatrixGroup_generic
from sage.structure.unique_representation import UniqueRepresentation

#from hecke_triangle_group_element import *


class HeckeTriangleGroup(FinitelyGeneratedMatrixGroup_generic, UniqueRepresentation):
    r"""
    Hecke triangle group (2, n, infinity).

    This is a stub implementation.
    """

#class HeckeTriangleGroup(MatrixSpace):
#    @staticmethod
#    def __classcall__(self,n):
#        return super(MatrixSpace,self).__classcall__(self,n)
#
#    Element=HeckeTriangleGroupElement
    def __init__(self,n):
        r"""
        Hecke triangle group (2, n, infinity).
        Namely the von Dyck group corresponding to the triangle group
        with angles (pi/2, pi/n, 0).

        INPUT:

        - ``n``   - ``infinity`` or an integer greater or equal to ``3``.

        OUTPUT:

        The Hecke triangle group for the given parameter ``n``.
        """

        if (n==infinity):
            self.n               = infinity
        else:
            self.n               = ZZ(n)
            if (self.n<3):
                raise AttributeError("n has to be infinity or an Integer >= 3.")
        self.lam                 = AA(2*cos(pi/self.n))
        self.rho                 = AlgebraicField()(exp(pi/self.n*i))
        self.alpha               = ZZ(1)/ZZ(2)*(ZZ(1)/ZZ(2)-ZZ(1)/self.n)
        self.beta                = ZZ(1)/ZZ(2)*(ZZ(1)/ZZ(2)+ZZ(1)/self.n)
        self.I                   = matrix(AA,[[1,0],[0,1]])
        self.T                   = matrix(AA,[[1,self.lam],[0,1]])
        self.S                   = matrix(AA,[[0,-1],[1,0]])
        self.U                   = self.T*self.S
        self.V                   = lambda j: self.U**(j-1)*self.T
        #self.element_class       = HeckeTriangleGroupElement
        FinitelyGeneratedMatrixGroup_generic.__init__(self,ZZ(2),AA,[self.S,self.T])
        #MatrixSpace.__init__(self,AA,ZZ(2))

#    def _get_matrix_class(self):
#        return Matrix_generic_dense
#        return HeckeTriangleGroupElement

    def dvalue(self):
        #TODO: Be more precise (transfinite diameter of what exactly)
        #TODO: Is d or 1/d the transfinite diameter?
        r"""
        Return the numerical (or exact in case n=3, 4, 6)
        value of the transfinite diameter (or capacity)
        of ``self``.
        """

        n=self.n
        if (n==3):
            return ZZ(1)/ZZ(2**6*3**3)
        elif (n==4):
            return ZZ(1)/ZZ(2**8)
        elif (n==6):
            return ZZ(1)/ZZ(2**2*3**3)
        elif (n==infinity):
            return ZZ(1)/ZZ(2**6)
        else:
            return exp(-ZZ(2)*psi1(ZZ(1))+psi1(ZZ(1)-self.alpha)+psi1(ZZ(1)-self.beta)-pi*sec(pi/self.n))

    def _repr_(self):
        r"""
        Return the string representation of ``self``.
        """

        return "Hecke triangle group for n = {}".format(self.n)

    def _latex_(self):
        r"""
        Return the LaTeX representation of ``self``.

        EXAMPLES::

            sage: a = HeckeTriangleGroup(5)
            sage: latex(a)
            \Gamma^{(5)}
        """

        return '\\Gamma^{(%s)}'%(latex(self.n))

    def is_arithmetic(self):
        r"""
        Return True if ``self`` is an arithmetic subgroup.

        EXAMPLES:

            sage: HeckeTriangleGroup(6).is_arithmetic()
            True
            sage: HeckeTriangleGroup(5).is_arithmetic()
            False
        """

        if (self.n in [ZZ(3),ZZ(4),ZZ(6),infinity]):
            return True
        else:
            return False

    # Maybe this should be implemented for elements of the matrix group instead,
    # using _l_action(self,t).
    def act(self,mat,t):
        r"""
        Return the image of ``t`` under the action of the matrix ``mat``
        by linear fractional transformations.

        INPUT:

        - ``mat`` -- An element of the Hecke triangle group (no check is performed
          though and the function works for more general matrices as well).

        - ``t`` -- A complex number or an element of AlgebraicField().

        EXAMPLES::

            sage: G=HeckeTriangleGroup(5)
            sage: G.act(G.S,AlgebraicField()(1+i/2))
            2/5*I - 4/5
        """

        return (mat[0][0]*t+mat[0][1])/(mat[1][0]*t+mat[1][1])

    # Returns (A,w,fact) such that:
    #   * w=act(A,z)
    #   * w lies in the (usual) strict fundamental domain of Gamma^lambda
    #   * factor "=" aut_factor(A,w)
    #
    def get_FD(self,z,aut_factor=None):
        r"""
        Return a tuple (A,w,fact) which determines how to map ``z``
        to the usual (strict) fundamental domain of ``self``.

        INPUT:

        - ``z`` -- a complex number or an element of AlgebraicField().

        - ``aut_factor`` -- ``None`` (default) or an automorphy factor.
            The automorphy factor is a function ``aut_factor(mat, t)``.

            ``aut_factor`` only has to be defined for ``mat`` beeing
            one of two generators ``mat=self.T``, `mat=self.S`` or their
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
            ....:     if (mat == G.T or mat == G.T.inverse()):
            ....:         return 1
            ....:     elif (mat == G.S or mat == G.S.inverse()):
            ....:         return t**4
            ....:     else:
            ....:         raise NotImplementedError
            sage: (A,w,fact) = G.get_FD(z,aut_factor)
            sage: fact == full_factor(A,w)
            True
        """

        I=self.I
        T=self.T
        S=self.S
        TI=self.T.inverse()

        A=I
        L=[]
        w=z
        while (abs(w)<ZZ(1) or abs(w.real())>self.lam/ZZ(2)):
            if (abs(w)<ZZ(1)):
                w=self.act(self.S,w)
                A=S*A
                L.append(-S)
            if (w.real()>=self.lam/ZZ(2)):
                w=self.act(TI,w)
                A=TI*A
                L.append(T)
            elif (w.real()<self.lam/ZZ(2)):
                w=self.act(T,w)
                A=T*A
                L.append(TI)
        if (w.real()==self.lam/ZZ(2)):
            w=self.act(TI,w)
            A=TI*A
            L.append(T)
        if (abs(w)==ZZ(1) and w.real()>ZZ(0)):
            w=self.act(S,w)
            A=S*A
            L.append(-S)

        if (aut_factor==None):
            new_factor=ZZ(1)
        else:
            B=I
            temp_w=self.act(A,z)
            new_factor=ZZ(1)
            for gamma in reversed(L):
                B=gamma*B
                new_factor*=aut_factor(gamma,temp_w)
                temp_w=self.act(gamma,temp_w)

        return (A.inverse(),self.act(A,z),new_factor)

    def in_FD(self,z):
        r"""
        Returns ``True`` if ``z`` lies in the (strict) fundamental
        domain of ``self``.

        EXAMPLES::

            sage: HeckeTriangleGroup(5).in_FD(CC(1.5/2+0.9*i))
            True
            sage: HeckeTriangleGroup(4).in_FD(CC(1.5/2+0.9*i))
            False
        """

        return self.get_FD(z)[0]==self.I


