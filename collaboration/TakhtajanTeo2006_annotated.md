> **Annotated copy (2026-10-28).** Markers `[ERRATUM …]` flag places where the memoir is wrong, `[IMPLICIT HYPOTHESIS …]` places where it uses an unstated hypothesis; details in `collaboration/ERRATA.md`. Line numbers in the markers refer to the original file.

<!-- page 1 of 136 -->

MEMOIRS of the

IV of the American Mathematical Society

Number 861

# Weil-Petersson Metric on the Universal Teichmüller Space

Leon A. Takhtajan
Lee-Peng Teo

AMERICAN MATHEMATICAL SOCIETY
THE BURGER
THEITCOE MIN
BUSTIN
FOUNDED 1988

September 2006 • Volume 183 • Number 861 (first of 4 numbers) • ISSN 0065-9266

American Mathematical Society
Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46:51.

<!-- page 2 of 136 -->

Weil-Petersson Metric on the Universal Teichmüller Space

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

<!-- page 3 of 136 -->

This page intentionally left blank

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

<!-- page 4 of 136 -->

Number 861

of the

# Weil-Petersson Metric on the Universal Teichmüller Space

Leon A. Takhtajan
Lee-Peng Teo

![Image block](doc:04478a7/tier:standard/page:4/block:5)

September 2006 • Volume 183 • Number 861 (first of 4 numbers) • ISSN 0065-9266

American Mathematical Society
Licensed to Tohoku University. Prepared on Thu Oct 22 08-57-39 ETB-2026 for 4th week of the IP 130-34-46.51.
Providence, Rhode Island

<!-- page 5 of 136 -->

![Image block](doc:04478a7/tier:standard/page:5/block:1)

2000 Mathematics Subject Classification. Primary 30F60; Secondary 30C55, 32G15, 46E20, 58B20, 58B25.

Library of Congress Cataloging-in-Publication Data

Takhtajan, Leon A.
Weil-Petersson metric on the universal Teichmüller space / Leon A. Takhtajan.
p. cm. — (Memoirs of the American Mathematical Society, ISSN 0065-9266 ; no. 861)
"Volume 183, number 861 (first of 4 numbers)."
Includes bibliographical references.
ISBN-13: 978-0-8218-3936-2 (alk. paper)

1. Teichmüller spaces. 2. Univalent functions. 3. Riemann surfaces. I. Teo, Lee-Peng, 1975–II. Title. III. Series.

QA3.A57 no. 861

[QA337]

510 s—dc22

[515'.94]

2006045733

## Memoirs of the American Mathematical Society

This journal is devoted entirely to research in pure and applied mathematics.

\*\*Subscription information.\*\* The 2006 subscription begins with volume 179 and consists of six mailings, each containing one or more numbers. Subscription prices for 2006 are US\$624 list, US\$499 institutional member. A late charge of 10% of the subscription price will be imposed on orders received from nonmembers after January 1 of the subscription year. Subscribers outside the United States and India must pay a postage surcharge of US\$31; subscribers in India must pay a postage surcharge of US\$43. Expedited delivery to destinations in North America US\$35; elsewhere US\$130. Each number may be ordered separately; \*please specify number\* when ordering an individual number. For prices and titles of recently released numbers, see the New Publications sections of the Notices of the American Mathematical Society.

Back number information. For back issues see the AMS Catalog of Publications.

Subscriptions and orders should be addressed to the American Mathematical Society, P.O. Box 845904, Boston, MA 02284-5904, USA. All orders must be accompanied by payment. Other correspondence should be addressed to 201 Charles Street, Providence, RI 02904-2294, USA.

Copying and reprinting. Individual readers of this publication, and nonprofit libraries acting for them, are permitted to make fair use of the material, such as to copy a chapter for use in teaching or research. Permission is granted to quote brief passages from this publication in reviews, provided the customary acknowledgment of the source is given.

Republication, systematic copying, or multiple reproduction of any material in this publication is permitted only under license from the American Mathematical Society. Requests for such permission should be addressed to the Acquisitions Department, American Mathematical Society, 201 Charles Street, Providence, Rhode Island 02904-2294, USA. Requests can also be made by e-mail to reprint-permission@ams.org.

Memoirs of the American Mathematical Society is published bimonthly (each volume consisting usually of more than one number) by the American Mathematical Society at 201 Charles Street, Providence, RI 02904-2294, USA. Periodicals postage paid at Providence, RI. Postmaster: Send address changes to Memoirs, American Mathematical Society, 201 Charles Street, Providence, RI 02904-2294, USA.

© 2006 by the American Mathematical Society. All rights reserved.
Copyright of this publication reverts to the public domain 28 years after publication. Contact the AMS for copyright status.
This publication is indexed in Science Citation Index®, SciSearch®, Research Alert®, CompuMath Citation Index®, Current Contents®/Physical, Chemical & Earth Sciences. Printed in the United States of America.

The paper used in this book is acid-free and falls within the guidelines established to ensure permanence and durability.
Visit the AMS home page at http://www.ams.org/

10 9 8 7 6 5 4 3 2 1 11 10 09 08 07 06
Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

<!-- page 6 of 136 -->

## Contents

- Introduction 1
- Chapter 1. Curvature Properties and Chern Forms 7
- 1. The universal Teichmüller space 7
- 1.1. Teichmüller theory 7
- 1.1.1. Main definitions 7
- 1.1.2. The group structure 8
- 1.1.3. The Bers embedding 9
- 1.1.4. The complex structure 9
- 1.1.5. The universal Teichmüller curve 10
- 1.2. Homogeneous spaces of $\mathrm{Homeo}_{qs}(S^1)$ 11
- 1.2.1. Conformal welding 11
- 1.2.2. The horizontal and vertical subspaces 14
- 1.2.3. The isomorphisms of the tangent spaces 15
- 1.3. Teichmüller spaces and Teichmüller curves of Fuchsian groups 17
- 1.4. Resolvent kernel 18
- 1.5. Variational formulas 19
- 2. $T(1)$ as a Hilbert manifold 22
- 2.1. Hilbert space structure on tangent spaces 22
- 2.2. The $L^2$-estimates 27
- 2.3. The Hilbert manifold structure of $T(1)$ 29
- 2.4. Integral manifolds of the distribution $\mathfrak{D}_T$ 31
- 3. $T_0(1)$ as a topological group 32
- 4. Velling-Kirillov and Weil-Petersson metrics 36
- 4.1. Velling-Kirillov metric on the universal Teichmüller curve 36
- 4.2. Weil-Petersson metric on the universal Teichmüller space 37
- 5. Characteristic forms of the universal Teichmüller curve 38
- 5.1. The form $c_1(V)$ as Velling-Kirillov symplectic form 39
- 5.2. The Chern form $c_1(V)$ and the resolvent kernel 41
- 5.3. Mumford-Morita-Miller characteristic forms 43
- 6. First and second variations of the hyperbolic metric 44
- 6.1. The first variation 44
- 6.2. The second variation 44
- 7. Riemann curvature tensor 46
- 7.1. The first variation of the Weil-Petersson metric 46
- 7.2. The second variation of the Weil-Petersson metric 50
- 7.3. Ricci and sectional curvatures 54
- 8. Finite-dimensional Teichmüller spaces 56
- Chapter 2. Kähler Potential and Period Mapping 65

V

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

<!-- page 7 of 136 -->

vi

CONTENTS

- 1. Hilbert spaces and univalent functions 65
- 2. Grunsky operators for $T_0(1)$ 70
- 2.1. Grunsky coefficients and operators 70
- 2.2. Fredholm eigenvalues and Fredholm determinant 78
- 2.3. Period matrix of 1-forms 82
- 3. Variations of the functions $S_1$ and $S_2$ 83
- 3.1. The first variation of $S_2$ 84
- 3.2. The first variation of $S_1$ 85
- 4. Weil-Petersson potential 95
- 4.1. Weil-Petersson potential on $T_0(1)$ 95
- 4.2. Weil-Petersson potential on $T(1)$ 97
- 5. The period mapping 97
- 5.1. KYNS period mapping 98
- 5.2. Embeddings into the Segal-Wilson universal Grassmannian 101
- Appendix A. The Hilbert Manifold Structure of $T_0(1)$ 105
- Appendix B. The Period Mapping $\hat{\mathcal{P}}$ 109
- Bibliography 117

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

<!-- page 8 of 136 -->

## Abstract

In this memoir, we prove that the universal Teichmüller space $T(1)$ carries a new structure of a complex Hilbert manifold and show that the connected component of the identity of $T(1)$ — the Hilbert submanifold $T_0(1)$ — is a topological group. We define a Weil-Petersson metric on $T(1)$ by Hilbert space inner products on tangent spaces, compute its Riemann curvature tensor, and show that $T(1)$ is a Kähler-Einstein manifold with negative Ricci and sectional curvatures. We introduce and compute Mumford-Miller-Morita characteristic forms for the vertical tangent bundle of the universal Teichmüller curve fibration over the universal Teichmüller space. As an application, we derive Wolpert curvature formulas for the finite-dimensional Teichmüller spaces from the formulas for the universal Teichmüller space. We study in detail the Hilbert manifold structure on $T_0(1)$ and characterize points on $T_0(1)$ in terms of Bers and pre-Bers embeddings by proving that the Grunsky operators $B_1$ and $B_4$, associated with the points in $T_0(1)$ via conformal welding, are Hilbert-Schmidt. We define a “universal Liouville action” — a real-valued function $S_1$ on $T_0(1)$, and prove that it is a Kähler potential of the Weil-Petersson metric on $T_0(1)$. We also prove that $S_1$ is $-\frac{1}{12\pi}$ times the logarithm of the Fredholm determinant of associated quasi-circle, which generalizes classical results of Schiffer and Hawley. We define the universal period mapping $\hat{\mathcal{P}}: T(1) \to \mathcal{B}(\ell^2)$ of $T(1)$ into the Banach space of bounded operators on the Hilbert space $\ell^2$, prove that $\hat{\mathcal{P}}$ is a holomorphic mapping of Banach manifolds, and show that $\hat{\mathcal{P}}$ coincides with the period mapping introduced by Kurillov and Yuriev and Nag and Sullivan. We prove that the restriction of $\hat{\mathcal{P}}$ to $T_0(1)$ is an inclusion of $T_0(1)$ into the Segal-Wilson universal Grassmannian, which is a holomorphic mapping of Hilbert manifolds. We also prove that the image of the topological group $S$ of symmetric homeomorphisms of $S^1$ under the mapping $\hat{\mathcal{P}}$ consists of compact operators on $\ell^2$.

The results of this memoir were presented in our e-prints: Weil-Petersson metric on the universal Teichmuller space I. Curvature properties and Chern forms, arXiv:math.CV/0312172 (2003), and Weil-Petersson metric on the universal Teichmuller space II. Kahler potential and period mapping, arXiv:math.CV/0406408 (2004).

<small><span class="docvortex-page-footnote" data-block-type="page_footnote" style="color:#6b7280">Received by the editor January 26, 2005.</span></small>

<small><span class="docvortex-page-footnote" data-block-type="page_footnote" style="color:#6b7280">2000 Mathematics Subject Classification. 30F60 (Primary) 30C55, 32G15, 46E20, 58B20, 58B25 (Secondary).</span></small>

<small><span class="docvortex-page-footnote" data-block-type="page_footnote" style="color:#6b7280">Key words and phrases. Universal Teichmüller space, Bers coordinates, Bers embedding, Hilbert manifold structure, Weil-Petersson metric, variation of the hyperbolic metric, Riemann curvature tensor, Grunsky operators, Kähler potential, Fredholm determinant, universal Liouville action, period mapping.</span></small>

vii

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

<!-- page 9 of 136 -->

This page intentionally left blank

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

<!-- page 10 of 136 -->

## Introduction

The universal Teichmüller space $T(1)$ is the simplest Teichmüller space that bridges spaces of univalent functions and general Teichmüller spaces. Introduced by Bers [Ber65, Ber72, Ber73], the universal Teichmüller space is an infinite-dimensional complex manifold modeled on a Banach space. It contains Teichmüller spaces of Riemann surfaces as complex submanifolds. The universal Teichmüller space $T(1)$ also came to the forefront with the advent of string theory. Its complex submanifold — an infinite-dimensional complex Fréchet manifold $\text{Möb}(S^1) \setminus \text{Diff}_+(S^1)$, plays an important role in one of the approaches to non-perturbative bosonic closed string field theory based on Kähler geometry [BR87a, BR87b]. The manifold $\text{Möb}(S^1) \setminus \text{Diff}_+(S^1)$ — a homogeneous space of the Lie group $\text{Diff}_+(S^1)$, also has an interpretation as a coadjoint orbit of the Bott-Virasoro group, and as such carries a natural right-invariant Kähler metric [Kir87, KY87].

The complex geometry of the finite-dimensional Teichmüller spaces — Teichmüller spaces $T(\Gamma)$ of cofinite Fuchsian groups, has been extensively studied in the context of Ahlfors-Bers deformation theory of complex structures on Riemann surfaces. In particular, A. Weil defined a natural Hermitian metric on $T(\Gamma)$ by the Petersson inner product on the tangent spaces. Called Weil-Petersson metric, it was shown to be a Kähler metric by Weil and Ahlfors. In his seminal paper [Ahl62] Ahlfors has studied the curvature properties of the Weil-Petersson metric. In particular, he proved that the Bers coordinates on $T(\Gamma)$ are geodesic at the origin, and computed the Riemann curvature tensor of the Weil-Petersson metric in terms of multiple principal value integrals. Using these formulas, Ahlfors proved that $T(\Gamma)$ has negative Ricci, holomorphic sectional, and scalar curvatures. Further results have been obtained by Royden [Roy75]. Wolpert re-examined Ahlfors' approach in [Wol86]. He developed a different method for computing Riemann and Ricci curvature tensors, and obtained explicit formulas in terms of the resolvent kernel of the Laplace operator of the hyperbolic metric on the corresponding Riemann surface.

Curvature properties of the infinite-dimensional manifold $\mathrm{Möb}(S^1) \backslash \mathrm{Diff}_+(S^1)$ have been studied by Kirillov and Yuriev [KY87], and by Bowick and Rajeev [BR87a, BR87b]. In particular, they computed the Riemann curvature tensor of the right-invariant Kähler metric and proved that $\mathrm{Möb}(S^1) \backslash \mathrm{Diff}_+(S^1)$ is a Kähler-Einstein manifold.

Since both the finite-dimensional Teichmüller spaces  $T(\Gamma)$  and the homogeneous space  $\mathrm{Möb}(S^{1})\backslash\mathrm{Diff}_{+}(S^{1})$  are complex submanifolds of  $T(1)$, it is natural to investigate whether the latter space carries a “universal” Kähler metric which can be pulled back to the submanifolds. The immediate difficulty is that the universal Teichmüller space  $T(1)$  is a complex Banach manifold, so that its tangent spaces do not carry Hermitian metric. Nag and Verjovsky [NV90] were the first to address this problem. They have shown that the Kähler metric on  $\mathrm{Möb}(S^{1})\backslash\mathrm{Diff}_{+}(S^{1})$

1

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

<!-- page 11 of 136 -->

2

INTRODUCTION

is the pull-back of a certain Hermitian metric defined on a Hilbert subspace of the tangent space at the origin of  $T(1)$ . The latter metric is analogous to the Weil-Petersson metric on finite-dimensional Teichmüller spaces. However, finite-dimensional Teichmüller spaces  $T(\Gamma)$  embed into  $T(1)$  transversally to the Hilbert subspace, so that the Weil-Petersson metric on  $T(\Gamma)$  can not be pulled back from  $T(1)$ . Nevertheless, following a suggestion by Velling, Nag and Verjovsky [NV90] have shown that the Weil-Petersson metric on  $T(\Gamma)$  can be obtained by a certain “averaging” procedure using Patterson’s uniform distribution of the “lattice points” of a cofinite Fuchsian group  $\Gamma$  in the hyperbolic plane. The major open problem is to define the Weil-Petersson metric on the whole space  $T(1)$ , to study its curvature properties, and to find relation between curvatures of this metric and the Weil-Petersson metric on finite-dimensional Teichmüller spaces $^{1}$ .

In this memoir, we introduce Weil-Petersson metric on the universal Teichmüller space $T(1)$ and study its curvature properties. In Chapter 1 we prove that $T(1)$ carries a new structure of a Hilbert manifold such that in the underlying topology $T(1)$ has uncountably many components. We prove that the connected component of the identity in $T(1)$, the Hilbert submanifold $T_0(1)$, is a topological group and describe its image under the Bers embedding $\beta : T(1) \to A_{\infty}(\mathbb{D})$. We define the Weil-Petersson metric on $T(1)$ by Hilbert space inner products on tangent spaces. We re-examine the Ahlfors original computation [Ahl62] of the second variation of the hyperbolic metric and of the Riemann tensor for the finite-dimensional Teichmüller spaces in terms of the principal value integrals. We show how to extend the Ahlfors' method to the case of the universal Teichmüller space and how to convert formulas using principal value integrals into closed expressions using resolvent kernel of the Laplace operator on the hyperbolic plane. Our results extend the Wolpert's formulas [Wol86] to the infinite-dimensional Hilbert manifold $T(1)$. We also prove that $T(1)$ is a Kähler-Einstein manifold with negative Ricci and sectional curvatures. Using the averaging procedure, we derive Wolpert's curvature formulas [Wol86] for the finite-dimensional Teichmüller spaces from the curvature formulas for the universal Teichmüller space. We introduce and compute Mumford-Morita-Miller characteristic forms for the vertical tangent bundle associated with the fibration $\pi : T(1) \to T(1)$, where $T(1)$ is the universal Teichmüller curve. Here again we consider $T(1)$ and $T(1)$ as Hilbert manifolds and show that the integration over the fibers operation, used in the definition of Mumford-Morita-Miller characteristic forms, is well-defined.

In Chapter 2 we study in detail the Hilbert manifold structure of $T(1)$ and establish relations between the Hilbert submanifold $T_0(1)$ — the connected component of the identity in $T(1)$, and classical Grunsky operators $B_l$, $l = 1,2,3,4$, associated with the conformal welding. We characterize $T_0(1)$ in terms of the pre-Bers embedding $\hat{\beta}: T(1) \to A_{\infty}^{1}(\mathbb{D})$ and prove that the Grunsky operators $B_1$ and $B_4$ associated with the points in $T_0(1)$ are Hilbert-Schmidt. We establish the relation between eigenvalues of Grunsky operators and classical Fredholm eigenvalues, generalizing Schiffer's result for $C^3$ curves [Sch81]. We prove that the logarithm of the Fredholm determinant of the operator $I - B_1B_1^*$ associated with points in $T_0(1)$ (or, which is the same, of the Fredholm determinant of $I - B_4B_4^*$) is, up to a constant, a Kähler potential for the Weil-Petersson metric on $T_0(1)$. We prove the

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

<small><span class="docvortex-page-footnote" data-block-type="page_footnote" style="color:#6b7280">$^{1}$ See the remark on p. 136 in [NV90].</span></small>

<!-- page 12 of 136 -->

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

INTRODUCTION

3

explicit formula for this Fredholm determinant, expressing it as the “universal Liouville action”. Using Grunsky operators, we define the universal period mapping $\mathcal{P}$ of $T_0(1)$ into the Hilbert space $\mathcal{S}_2$ of Hilbert-Scmidt operators on the Hilbert space $\ell^2$, as well as the mapping $\hat{\mathcal{P}}$ of $T(1)$ into the Banach space $\mathcal{B}(\ell^2)$ of bounded operators on $\ell^2$. We prove that $\mathcal{P}$ and $\hat{\mathcal{P}}$ are holomorphic mappings of Hilbert and Banach manifolds respectively. We show that the mapping $\hat{\mathcal{P}}$ coincides with the period mapping, first introduced by Kirillov and Yuriev [KY88] for the homogenous space $\mathrm{Möb}(S^1)\backslash\mathrm{Diff}_+(S^1)$, studied in detail by Nag [Nag92], and then extended to $T(1)$ by Nag and Sullivan [NS95]$^2$. Finally, we prove that the image of the topological group $S$ of symmetric homeomorphisms of $S^1$ under the period mapping $\hat{\mathcal{P}}$ is $\mathcal{S}_{\infty}\cap\hat{\mathcal{P}}(T(1))$, where $\mathcal{S}_{\infty}$ is the ideal of the Banach algebra $\mathcal{B}(\ell^2)$ consisting of compact operators on $\ell^2$.

Here is the more detailed content of the paper, starting with Chapter 1. In Section 1 we present necessary facts from Teichmüller theory, mainly following classical monographs by Ahlfors [Ahl87], Lehto [Leh87] and Nag [Nag88]. Namely, in Section 1.1 we briefly cover: the main definitions, the group structure of the universal Teichmüller space $T(1)$, the Bers embedding, structure of $T(1)$ as an infinite-dimensional complex Banach manifold modeled on the complex Banach space $A_{\infty}(\mathbb{D})$, and the basic properties of the universal Teichmüller curve $\pi : \mathcal{T}(1) \to T(1)$. In Section 1.2 we realize $T(1)$ and $\mathcal{T}(1)$ as homogeneous spaces of the group $\mathrm{Homeo}_{qs}(S^1)$ of quasi-symmetric homeomorphisms of $S^1$, and by using conformal welding we identify $T(1)$ and $\mathcal{T}(1)$ with the spaces of univalent functions on the unit disk $\mathbb{D}$. We describe the decomposition of the tangent bundle of $\mathcal{T}(1)$ over the fiber $\pi^{-1}(0)$ and present isomorphisms between the tangent spaces. Lemma 1.5 which describes a special property of the quasiconformal mapping with harmonic Beltrami differential seems to be a new result. In Section 1.3 we present, in a succinct form, basic facts about the Teichmüller spaces and Teichmüller curves of Fuchsian groups, including the definition of the Weil-Petersson metric, and Patterson's lemma on the uniform distribution of lattice points on the hyperbolic plane. In Section 1.4 we collect necessary properties of the resolvent kernel $G = \frac{1}{2} (\Delta_0 + \frac{1}{2})^{-1}$ of the Laplace operator $\Delta_0$ on the hyperbolic plane, and in Section 1.5 we present Ahlfors' classical variational formulas. In Section 2 we introduce new Hilbert manifold structure on $T(1)$. Namely, in Section 2.1 we define the Hilbert subspaces $H^{-1,1}(\mathbb{D}^*)$ and $A_2(\mathbb{D})$ of the tangent spaces to $T(1)$ and to $A_{\infty}(\mathbb{D})$. In Theorem 2.3 we prove that the differential of the Bers embedding $\beta : T(1) \to A_{\infty}(\mathbb{D})$ is a bounded bijection between these Hilbert spaces. In Section 2.2 we prepare all $L^2$-estimates used in Section 2.3. The main result there is Theorem 2.10 — the existence of a Hilbert manifold atlas for $T(1)$. In Theorem 2.13 we prove that the Bers embedding is also a biholomorphic mapping of Hilbert manifolds. In Section 3 we prove that $T_0(1)$ and the corresponding Teichmüller curve $\mathcal{T}_0(1)$ — the inverse image of $T_0(1)$ under the projection $\pi$, are topological groups in the Hilbert manifold topology. Moreover, we show that $T_0(1)$ is the closure of $\mathrm{Möb}(S^1)\backslash \mathrm{Diff}_+(S^1)$ in $T(1)$ with respect to this topology, and prove that $T_0(1)$ is the inverse image of $\beta (T(1))\cap A_2(\mathbb{D})$ under the Bers embedding. In Section 4.1, following [Teo04], we recall the definition of the Velling-Kirillov metric on the universal Teichmüller curve $\mathcal{T}(1)$ considered as a Banach manifold, and in

<small><span class="docvortex-page-footnote" data-block-type="page_footnote" style="color:#6b7280">ˆP</span></small>

<small><span class="docvortex-page-footnote" data-block-type="page_footnote" style="color:#6b7280">$^{2}$ It is explained in [Nag92] and [NS95] it what sense the mapping  $\hat{P}$  generalizes the classical period mapping of compact Riemann surfaces.</span></small>

<!-- page 13 of 136 -->

4

INTRODUCTION

Section 4.2 we define the Weil-Petersson metric on the Hilbert manifold $T(1)$. In Section 5.1 we prove that Velling-Kirillov metric is real-analytic on $\mathcal{T}(1)$ by explicitly constructing its real-analytic Kähler potential — Theorem 5.3. We introduce Mumford-Miller-Morita characteristic forms by considering $\pi : \mathcal{T}(1) \to T(1)$ as a fibration of Hilbert manifolds. The latter property is crucial for the operation “integration over the fibers” (which are non-compact) to be well-defined. In Theorem 5.10 we explicitly compute Mumford-Miller-Morita forms in terms of the resolvent $G$. This is an infinite-dimensional generalization of Wolpert's result in [Wol86]. In Section 6 we give a simple derivation of the second variation of the hyperbolic metric — Proposition 6.3. In Section 7 we prove that the Weil-Petersson metric on $T(1)$ is Kähler and explicitly compute its Riemann and Ricci curvature tensors, showing that $T(1)$ is a Kähler-Einstein manifold. The main results there are Theorem 7.7 and 7.11. They are based on a more technical Proposition 7.2 and Lemma 7.8. In Section 8 we derive Wolpert's curvature formulas [Wol86] for finite-dimensional Teichmüller spaces from the corresponding “universal” curvature formulas for $T(1)$, obtained in Section 7.

In Section 1 of Chapter 2 we characterize the univalent functions associated with the Hilbert manifold $T_0(1)$ in terms of the Hilbert spaces $A_2^1(\mathbb{D})$ and $A_2^1(\mathbb{D}^*)$ of holomorphic functions on $\mathbb{D}$ and $\mathbb{D}^*$ respectively, square integrable with respect to the Lebesgue measure. Using the embedding $A_2^1(\mathbb{D}) \hookrightarrow A_\infty^1(\mathbb{D})$ into the Banach space of holomorphic functions on $\mathbb{D}$, the Becker-Pommerenke theorem [BP78], and the characterization of the topological group $S$ of symmetric homeomorphisms of $S^1$ given by Gardiner and Sullivan [GS92], we prove that $T_0(1)$ is a subgroup of $S$. The main result of this section is Theorem 1.12, which states that $[\mu] \in T_0(1)$ if and only if one of the following conditions holds: (i) $\mathcal{S}(\mathrm{f}^{\mu}) \in A_2(\mathbb{D})$; (ii) $\mathcal{A}(\mathrm{f}^{\mu}) \in A_2^1(\mathbb{D})$; (iii) $\mathcal{S}(\mathrm{g}_{\mu}) \in A_2(\mathbb{D}^*)$; (iv) $\mathcal{A}(\mathrm{g}_{\mu}) \in A_2^1(\mathbb{D}^*)$. Here $\mathcal{S}(f)$ is the Schwarzian derivative of the univalent function $f$, and

$$
\mathcal {A} (f) = \frac {f ^ {\prime \prime}}{f ^ {\prime}}.
$$

This theorem allows us to introduce the “universal Liouville action” — the function  $S_{1}: T_{0}(1) \to \mathbb{R}$ , defined by

$$
\left| \mathsf {S} _ {1} ([ \mu ]) = \iint_ {\mathbb {D}} | \mathcal {A} (\mathrm{f} ^ {\mu}) | ^ {2} d ^ {2} z + \iint_ {\mathbb {D} ^ {*}} | \mathcal {A} (\mathrm{g} _ {\mu}) | ^ {2} d ^ {2} z - 4 \pi \log | \mathrm{g} _ {\mu} ^ {\prime} (\infty) |. \right.\tag{0.1}
$$

In Section 2 to every $[\mu] \in T(1)$ we assign the Grunksy operators $B_1, B_2, B_3$ and $B_4$, associated with the corresponding pair $(\mathrm{f}^{\mu}, \mathrm{g}_{\mu})$ of univalent functions. The Lebesgue measure of the quasi-circle $\mathbb{C} \setminus \{f(\mathbb{D}) \cup g(\mathbb{D}^{*})\}$ is zero, so that the generalized Grunsky inequality [Hum72, Pom92] can be succinctly formulated as the unitarity of the operator $\mathbf{B} = \begin{pmatrix} B_1 & B_2 \\ B_3 & B_4 \end{pmatrix}$ on $\ell^2 \oplus \ell^2$. The main result of Section 2.1 is Theorem 2.6, which states (see Corollary 2.9) that $[\mu] \in T_0(1)$ if and only if the corresponding Grunsky operators $B_1(\mathrm{f}^{\mu}), B_4(\mathrm{g}_{\mu}) \in \mathcal{S}_2$ — the Hilbert space of Hilbert-Schmidt operators on $\ell^2$. In Theorem 2.10 we prove that the mapping $\mathcal{P}: T_0(1) \to \mathcal{S}_2$, defined by $\mathcal{P}([\mu]) = B_1(\mathrm{f}^{\mu})$, is a holomorphic mapping of Hilbert manifolds. Extended to the universal Teichmüller space $T(1)$, this defines, as we prove in Appendix B, a holomorphic mapping $\hat{\mathcal{P}}: T(1) \to \mathcal{B}(\ell^2)$ of Banach manifolds. In Section 2.2 we show that for $[\mu] \in T_0(1)$ the eigenvalues of the corresponding trace class operators $B_1B_1^*$ and $B_4B_4^*$ are related to the eigenvalues

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026for download from IP 130.34.46.51.

<!-- page 14 of 136 -->

INTRODUCTION

5

of the classical Poincaré-Fredholm integral operator associated with the quasi-circle $\mathcal{C} = \mathrm{f}^{\mu}(S^{1}) = \mathrm{g}_{\mu}(S^{1})$. Since for $[\mu] \in T_0(1)$ these quasi-circles contain all $C^3$ curves, this generalizes Schiffer's result [Sch81]. Extending [Sch59], we introduce the Fredholm determinant $\operatorname{Det}_F(\mathcal{C})$ of the quasi-circle $\mathcal{C}$ as the Fredholm determinant $\det(I - B_1B_1^*) = \det(I - B_4B_4^*)$, and define the function $S_2: T_0(1) \to \mathbb{R}$ by

$$
\mathrm{S} _ {2} ([ \mu ]) = \log \operatorname{Det} _ {F} (\mathrm{f} ^ {\mu} (S ^ {1})), [ \mu ] \in T (1).\tag{0.2}
$$

In Section 2.3 we define the semi-infinite period matrices of 1-forms for natural bases of $A_2^1(\mathbb{D})$ and $A_2^1(\mathbb{D}^*)$, which generalize imaginary parts of the classical period matrices for compact Riemann surfaces, and show that they correspond to the operators $B_2B_2^*$ and $B_3B_3^*$.

In Section 3 we compute the “first variations” of the functions  $S_{1}$  and  $S_{2}$  — the  $(1,0)$ -forms  $\partial S_{1}$  and  $\partial S_{2}$ , where  $\partial$  is the  $(1,0)$ -component of the de Rham differential on the Hilbert manifold  $T_{0}(1)$ . Namely, we show in Theorems 3.5 and 3.1 (see Corollaries 3.9 and 3.2) that

$$
\partial \mathrm{S} _ {1} = 2 \boldsymbol {\vartheta} \quad \text {and} \quad \partial \mathrm{S} _ {2} = - \frac {1}{6 \pi} \boldsymbol {\vartheta},\tag{0.3}
$$

where the $(1,0)$-form $\vartheta$ on $T_0(1)$, under the natural isomorphism $T_{[\mu]}^* T_0(1) \simeq A_2(\mathbb{D}^*)$, is given by

$$
\boldsymbol {\vartheta} _ {[ \mu ]} = \mathcal {S} (\mathrm{g} _ {\mu}).\tag{0.4}
$$

The proof of Theorem 3.1 is rather standard, whereas the proof of Theorem 3.5 relies heavily on the identity given in Lemma 3.6. The latter can be interpreted as an extension of the generalized Grunsky equality to pairs of univalent functions $(\mathrm{f}^{\mu},\mathrm{g}_{\mu})$ for $[\mu ]\in T_0(1)$, which we consider quite interesting. Since the functions $\mathsf{S}_1$ and $\mathsf{S}_2$ on $T_0(1)$ both vanish at $0\in T_0(1)$, from (1.3) we immediately obtain that

$$
S _ {2} = - \frac {1}{1 2 \pi} S _ {1},
$$

thus expressing the Fredholm determinant as the universal Liouville action. In Corollary 3.12 and Remark 3.13 we interpret this relation as a surgery type formula for the determinants of elliptic operators on domains on the Riemann sphere $\mathbb{P}^1$.

In Section 4 we show that the relation (1.3) implies that the function $S_1$ is a Kähler potential of the Weil-Petersson metric on $T_0(1)$. The proof goes along the same lines as in the case of finite-dimensional Teichmüller spaces [TT03]. This explains why the function $S_1$ is called the universal Liouville action. In Section 5 we study the period mapping $\hat{\mathcal{P}}: T(1) \to \mathcal{B}(\ell^2)$. We prove that it coincides with the Kirillov-Yuriev-Nag-Sullivan mapping of $T(1)$ into the infinite-dimensional analog of Siegel disk $\mathfrak{D}_{\infty}$. We also show that the period mapping $\mathcal{P}: T_0(1) \to \mathcal{S}_2$ gives an embedding of $T_0(1)$ into the Segal-Wilson universal Grassmannian.

In Appendix A we study the Hilbert manifold structure on the topological group  $\mathcal{T}_{0}(1)$  — the pre-image of the Hilbert manifold  $T_{0}(1)$  under the canonical projection  $\pi : \mathcal{T}(1) \to T(1)$ . We prove in Theorem A.3 that the Bers embedding  $\beta : \mathcal{T}_{0}(1) \to A_{2}(\mathbb{D}) \oplus \mathbb{C}$  and the pre-Bers embedding  $\hat{\beta} : \mathcal{T}_{0}(1) \to A_{2}^{1}(\mathbb{D})$  induce the same Hilbert manifold structure on  $\mathcal{T}_{0}(1)$ . This result is parallel to the one proved in the Appendix of [Teo04]. We also prove Corollaries A.4 and A.6, characterizing convergence in the Hilbert manifold topology of  $\mathcal{T}_{0}(1)$ , which were used in the proof of Lemma 4.6. Finally, in Appendix B we show that  $\hat{\mathcal{P}} : T(1) \to \mathcal{B}(\ell^{2})$  is a holomorphic mapping of Banach manifolds and prove that the image of the

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026for download from IP 130.34.46.51.

<!-- page 15 of 136 -->

6

INTRODUCTION

topological group $S$ under the map $\hat{\mathcal{P}}$ is the subset $\mathcal{S}_{\infty} \cap \hat{\mathcal{P}}(T(1))$ of $\mathcal{B}(\ell^2)$. The properties of the tower of embedded manifolds $T_0(1) \hookrightarrow S \hookrightarrow T(1)$ are summarized in a commutative diagram at the end of Appendix B.

Acknowledgments. We appreciate useful discussions with C. Bishop and especially with M. Luybich. The second author would like to thank P.Y. Wu for helpful discussions about operator theory. The work of the first author was partially supported by the NSF grant DMS-0204628. The work of the second author was partially supported by the grants NSC 91-2115-M-009-017 and NSC 92-2115-M-009-017. The second author also thanks CTS for the fellowship to visit Stony Brook University in the Summer of 2003, where a part of this work was done.

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

<!-- page 16 of 136 -->

## CHAPTER 1

## Curvature Properties and Chern Forms

## 1. The universal Teichmüller space

1.1. Teichmüller theory. Here we present, in a succinct form, necessary facts from Teichmüller theory (for more details, see monographs [Ahl87, Leh87, Nag88] and the exposition in [Teo04]).

1.1.1. Main definitions. Let $\mathbb{D} = \{z\in \mathbb{C}:|z| < 1\}$ be the open unit disk and let $\mathbb{D}^* = \{z\in \mathbb{C}:|z| > 1\}$ be its exterior. Denote by $L^{\infty}(\mathbb{D}^{*})$ and $L^{\infty}(\mathbb{D})$ the complex Banach spaces of bounded Beltrami differentials on $\mathbb{D}^*$ and $\mathbb{D}$ respectively, and let $L^{\infty}(\mathbb{D}^{*})_{1}$ be the open unit ball in $L^{\infty}(\mathbb{D}^{*})$. Two classical models of the universal Teichmüller space $T(1)$ are the following.

Model A. Extend every $\mu \in L^{\infty}(\mathbb{D}^{*})_{1}$ to $\mathbb{D}$ by the reflection

$$
\mu (z) = \overline {{\mu \left(\frac {1}{\bar {z}}\right)}} \frac {z ^ {2}}{\bar {z} ^ {2}}, z \in \mathbb {D},\tag{1.1}
$$

and consider the unique quasiconformal (q.c.) mapping $w_{\mu} : \mathbb{C} \to \mathbb{C}$, which fixes $-1, -i$ and $1$ (i.e., is normalized) and satisfies the Beltrami equation

$$
(w _ {\mu}) _ {\bar {z}} = \mu (w _ {\mu}) _ {z}.
$$


> **[IMPLICIT HYPOTHESIS W2-08]** (353, 449, 645, 1610; Lean: `wA_mapsTo`, `wA_mul`, `welding_of_wA`, `fiber_welding`, `Lemma25Prop`, `eq_1_10` (S1_1:1700, S1_1_Completed:51, HomogeneousCompleted:23–53, S2:1944)) `w_μ(∞)` is a finite point of `𝔻*` in general; the memoir treats `w_μ \| 𝔻*` as finite everywhere (Lemma 2.5, TT:1610–1630, derivative estimates on all of `𝔻*`) — implicit "away from the pole".

Here and in what follows subscripts $z$ and $\bar{z}$ always stand for the partial derivatives $\frac{\partial}{\partial z}$ and $\frac{\partial}{\partial\bar{z}}$, unless it is explicitly stated otherwise. Due to the reflection symmetry (1.1) the q.c. mapping $w_{\mu}$ satisfies

$$
\frac {1}{w _ {\mu} (z)} = \overline {{w _ {\mu} \left(\frac {1}{\bar {z}}\right)}}\tag{1.2}
$$

and fixes domains $\mathbb{D}$, $\mathbb{D}^*$, and the unit circle $S^1$. For $\mu, \nu \in L^{\infty}(\mathbb{D}^{*})_{1}$, set $\mu \sim \nu$ if $w_{\mu}|_{S^1} = w_{\nu}|_{S^1}$. The universal Teichmüller space $T(1)$ is defined as a set of equivalence classes of normalized q.c. mappings $w_{\mu}$,

$$
T (1) = L ^ {\infty} (\mathbb {D} ^ {*}) _ {1} / \sim .
$$

Model B. Extend every $\mu \in L^{\infty}(\mathbb{D}^{*})_{1}$ to be zero outside $\mathbb{D}^*$, and consider the unique q.c. mapping $w^{\mu}$ which satisfies the Beltrami equation

$$
w _ {\bar {z}} ^ {\mu} = \mu w _ {z} ^ {\mu},
$$

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

and is normalized by the conditions $f(0) = 0$, $f'(0) = 1$ and $f''(0) = 0$. Here $f = w^{\mu}|_{\mathbb{D}}$ is holomorphic on $\mathbb{D}$ and prime stands for the derivative. For $\mu, \nu \in L^{\infty}(\mathbb{D}^{*})_{1}$, set $\mu \sim \nu$ if $w^{\mu}|_{\mathbb{D}} = w^{\nu}|_{\mathbb{D}}$. The universal Teichmüller space $T(1)$ is defined as a set of equivalence classes of normalized q.c. mappings $w^{\mu}$,


> **[ERRATUM W2-01]** (374, 598, 632; Lean: `IsNormalizedB`, `wB`, `fB` (S1_1:511–528)) `f''(0)=0` is not always attainable by a finite-valued holomorphic `f`: the renormalizing Möbius map can have its pole in `w(𝔻)` (univalent `z(1−3z/4)/(1−1249z²/1296)`, `f''(0) = −3/2`, forced pole `4/3` at `z = 9/10`; `collaboration/lean2_normalization_pole_diagnostic.lean`). Correct: welding normalization (always exists, class-invariant).

$$
T (1) = L ^ {\infty} (\mathbb {D} ^ {*}) _ {1} / \sim .
$$

Since $w_{\mu}|_{S^1} = w_{\nu}|_{S^1}$ if and only if $w^{\mu}|_{\mathbb{D}} = w^{\nu}|_{\mathbb{D}}$, these two definitions of the universal Teichmüller space are equivalent. The set $T(1)$ is a topological space with

7

<!-- page 17 of 136 -->

8

1. CURVATURE PROPERTIES AND CHERN FORMS

the quotient topology induced from $L^{\infty}(\mathbb{D}^{*})_{1}$. Denote by $\mathcal{L}^{\infty}(\mathbb{D}^{*})$ the subspace of $L^{\infty}(\mathbb{D}^{*})$ consisting of real-analytic Beltrami differentials. Every point in $T(1)$ can be represented by $\mu \in \mathcal{L}^{\infty}(\mathbb{D}^{*})$ [Leh87, Sect. III.1.1].

The space $T(1)$ has a unique structure of a complex Banach manifold, such that the projection map

$$
\Phi : L ^ {\infty} (\mathbb {D} ^ {*}) _ {1} \to T (1)
$$

is a holomorphic submersion. The differential of $\Phi$ at the origin

$$
D _ {0} \Phi : L ^ {\infty} (\mathbb {D} ^ {*}) \to T _ {0} T (1)
$$

is a complex linear surjection of holomorphic tangent spaces. The kernel of $D_0\Phi$ is the subspace $\mathcal{N}(\mathbb{D}^*)$ of infinitesimally trivial Beltrami differentials. Explicitly,


> **[IMPLICIT HYPOTHESIS W1-26]** (404–413; Lean: `AOneStar` (Basic)) [CORRECTION 2026-10-25] A₁ should consist of integrable quadratic differentials regular at ∞. With the literal definition, ζ⁻³ ∈ A₁ (integrable on 𝔻*), so 𝓝 is too small and "ker D₀Φ = 𝓝" is false (下属5). Classed H because the memoir clearly means quadratic differentials; if read literally, TT:413 is a P.

$$
\mathcal {N} (\mathbb {D} ^ {*}) = \left\{\mu \in L ^ {\infty} (\mathbb {D} ^ {*}): \iint_ {\mathbb {D} ^ {*}} \mu   \phi   d ^ {2} z = 0 \text {for all} \phi \in A _ {1} (\mathbb {D} ^ {*}) \right\},
$$

where $d^2 z = dx\wedge dy,z = x + iy$ , and

$$
A _ {1} (\mathbb {D} ^ {*}) = \left\{\phi \text {holomorphic on} \mathbb {D} ^ {*}: \iint_ {\mathbb {D} ^ {*}} | \phi | d ^ {2} z <   \infty \right\}.
$$

The Banach space of bounded harmonic Beltrami differentials on $\mathbb{D}^*$ is defined by

$$
\Omega^ {- 1, 1} (\mathbb {D} ^ {*}) = \left\{\mu \in L ^ {\infty} (\mathbb {D} ^ {*}): \mu (z) = (1 - | z | ^ {2}) ^ {2} \overline {{\phi (z)}}, \phi \in A _ {\infty} (\mathbb {D} ^ {*}) \right\},
$$

where

$$
A _ {\infty} (\mathbb {D} ^ {*}) = \left\{\phi \text {holomorphic on} \mathbb {D} ^ {*}: \| \phi \| _ {\infty} = \sup _ {z \in \mathbb {D} ^ {*}} \big | (1 - | z | ^ {2}) ^ {2} \phi (z) \big | <   \infty \right\}.
$$

The Banach space $\Omega^{-1,1}(\mathbb{D}^*)$ is not separable. The decomposition

$$
L ^ {\infty} (\mathbb {D} ^ {*}) = \mathcal {N} (\mathbb {D} ^ {*}) \oplus \Omega^ {- 1, 1} (\mathbb {D} ^ {*})\tag{1.3}
$$

identifies the holomorphic tangent space $T_0T(1) = L^\infty(\mathbb{D}^*) / \mathcal{N}(\mathbb{D}^*)$ at the origin of $T(1)$ with the Banach space $\Omega^{-1,1}(\mathbb{D}^*)$. The universal Teichmüller space $T(1)$ is a complex Banach manifold modeled on $\Omega^{-1,1}(\mathbb{D}^*)$.

REMARK 1.1. Traditionally, the universal Teichmüller space is defined using the complex Banach space $L^{\infty}(\mathbb{D})_1$. The reflection (1.1) establishes natural complex anti-linear isomorphism between $L^{\infty}(\mathbb{D}^{*})_{1}$ and $L^{\infty}(\mathbb{D})_{1}$, and the universal Teichmüller space in the traditional definition is complex conjugate to the space $T(1)$ defined above.

1.1.2. The group structure. The unit ball $L^{\infty}(\mathbb{D}^{*})_{1}$ carries a group structure induced by the composition of q.c. mappings. The group law

$$
\lambda = \nu * \mu^ {- 1}
$$

is defined through $w_{\lambda} = w_{\nu} \circ w_{\mu}^{-1}$, where $\mu^{-1}$ stands for the inverse element to $\mu$, i.e., $\mu * \mu^{-1} = 0$. The group law is given explicitly by

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026for download from IP 130.34.46.51.

$$
\lambda = \left(\frac {\nu - \mu}{1 - \bar {\mu} \nu} \frac {(w _ {\mu}) _ {z}}{(\overline {{w}} _ {\mu}) _ {\bar {z}}}\right) \circ w _ {\mu} ^ {- 1}.
$$

It follows from this formula that $\mathcal{L}^{\infty}(\mathbb{D}^{*})_{1}$ is a subgroup of $L^{\infty}(\mathbb{D}^{*})_{1}$.

<!-- page 18 of 136 -->

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026for download from IP 130.34.46.51.

1. THE UNIVERSAL TEICHMÜLLER SPACE

9

For every $\lambda \in L^{\infty}(\mathbb{D}^{*})_{1}$ set $[\lambda] = \Phi (\lambda)\in T(1)$. The group structure on $L^{\infty}(\mathbb{D}^{*})_{1}$ projects to $T(1)$ by $[\lambda]*[\mu] = [\lambda *\mu]$. For every $\mu \in L^{\infty}(\mathbb{D}^{*})_{1}$ the right translations

$$
R _ {[ \mu ]}: T (1) \to T (1), \quad [ \lambda ] \mapsto [ \lambda * \mu ],
$$

are biholomorphic automorphisms of $T(1)$. The left translations, in general, are not even continuous mappings (see, e.g., [Leh87, Sect. III.3.4]). For every $\mu \in L^{\infty}(\mathbb{D}^{*})_{1}$ the kernel of $D_{\mu}\Phi$ is the subspace $D_0R_\mu (\mathcal{N}(\mathbb{D}^*))$ of $L^{\infty}(\mathbb{D}^{*})$ and

$$
T _ {[ \mu ]} T (1) = D _ {0} R _ {[ \mu ]} \left(T _ {0} T (1)\right) \simeq D _ {0} R _ {\mu} \left(\Omega^ {- 1, 1} (\mathbb {D} ^ {*})\right).
$$

1.1.3. The Bers embedding. Let $A_{\infty}(\mathbb{D})$ be the complex Banach space

$$
A _ {\infty} (\mathbb {D}) = \left\{\phi \text {holomorphic on} \mathbb {D}: \| \phi \| _ {\infty} = \sup _ {z \in \mathbb {D}} \big | (1 - | z | ^ {2}) ^ {2} \phi (z) \big | <   \infty \right\}.
$$

The Bers embedding $\beta : T(1) \hookrightarrow A_{\infty}(\mathbb{D})$ is defined as follows. Denote by $\mathcal{S}(f)$ the Schwarzian derivative of a conformal map $f$,

$$
\mathcal {S} (f) = \frac {f _ {z z z}}{f _ {z}} - \frac {3}{2} \left(\frac {f _ {z z}}{f _ {z}}\right) ^ {2}.
$$

For every $\mu \in L^{\infty}(\mathbb{D}^{*})_{1}$ the holomorphic function $\mathcal{S}(w^{\mu}|_{\mathbb{D}})\in A_{\infty}(\mathbb{D})$ (by Kraus-Nehari inequality it lies in the ball of radius 6 in $A_{\infty}(\mathbb{D})$). Set

$$
\beta ([ \mu ]) = \mathcal {S} (w ^ {\mu} | _ {\mathbb {D}}).
$$

The Bers embedding is a holomorphic map of complex Banach manifolds, and its differential at the origin is

$$
D _ {0} \beta (\mu) (z) = - \frac {6}{\pi} \iint_ {\mathbb {D} ^ {*}} \frac {\mu (\zeta)}{(\zeta - z) ^ {4}} d ^ {2} \zeta .\tag{1.4}
$$

The complex-linear mapping $D_0\beta$ induces the isomorphism $\Omega^{-1,1}(\mathbb{D}^*) \xrightarrow{\sim} A_\infty(\mathbb{D})$ of the holomorphic tangent spaces to $T(1)$ and $A_\infty(\mathbb{D})$ at the origin. The mapping $\Lambda : A_\infty(\mathbb{D}) \to \Omega^{-1,1}(\mathbb{D}^*)$, inverse to $D_0\beta$, is given by

$$
\mu (z) = \Lambda (\phi) (z) = - \frac {1}{2} \left(1 - | z | ^ {2}\right) ^ {2} \phi \left(\frac {1}{\bar {z}}\right) \frac {1}{\bar {z} ^ {4}}.
$$

According to the Ahlfors-Weill theorem, over the ball of radius 2 in $A_{\infty}(\mathbb{D})$ the map $\phi \mapsto [\Lambda (\phi)]$ is the right inverse to $\beta$, $\beta \circ \Lambda = \mathrm{id}$.

1.1.4. The complex structure. For every $\mu \in L^{\infty}(\mathbb{D}^{*})_{1}$ let $U_{\mu} \subset T(1)$ be the image of the ball of radius 2 in $A_{\infty}(\mathbb{D})$ under the map $h_{\mu}^{-1} = \Phi \circ R_{\mu} \circ \Lambda$. The maps $h_{\mu \nu} = h_{\mu} \circ h_{\nu}^{-1}: h_{\nu}(U_{\mu} \cap U_{\nu}) \to h_{\mu}(U_{\mu} \cap U_{\nu})$ are biholomorphic as functions on the Banach space $A_{\infty}(\mathbb{D})$. The structure of $T(1)$ as a complex Banach manifold modeled on the Banach space $A_{\infty}(\mathbb{D})$ is explicitly described by the complex-analytic atlas given by the open covering

$$
T (1) = \bigcup_ {\mu \in L ^ {\infty} \left(\mathbb {D} ^ {*}\right) _ {1}} U _ {\mu}
$$

with coordinate maps $h_\mu$ and transition maps $h_{\mu \nu}$. The canonical projection $\Phi : L^{\infty}(\mathbb{D}^{*})_{1} \to T(1)$ is a holomorphic submersion and the Bers embedding $\beta : T(1) \to A_{\infty}(\mathbb{D})$ is a biholomorphic map with respect to this complex structure.

REMARK 1.2. Since every point $T(1)$ can be represented by a real-analytic Beltrami differential, it is sufficient to consider the atlas formed by the charts $(U_{\mu}, h_{\mu})$ with $\mu \in \mathcal{L}^{\infty}(\mathbb{D}^{*})_{1}$.

<!-- page 19 of 136 -->

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026for download from IP 130.34.46.51.

10

1. CURVATURE PROPERTIES AND CHERN FORMS

Complex coordinates on $T(1)$ defined by the coordinate charts $(U_{\mu}, h_{\mu})$ are called Bers coordinates. For every $\nu \in \Omega^{-1,1}(\mathbb{D}^*)$ set $\phi = D_0\beta(\nu)$ and define a holomorphic vector field $\frac{\partial}{\partial\varepsilon_{\nu}}$ on $U_0$ by setting

$$
D h _ {0} \left(\frac {\partial}{\partial \varepsilon_ {\nu}}\right) = \phi
$$

at all points in  $U_{0}^{1}$ . At every point  $[\mu] \in U_{0}$ , identified with the corresponding harmonic Beltrami differential  $\mu$ , the vector field  $\frac{\partial}{\partial\varepsilon_{\nu}}$  in terms of the Bers coordinates on  $U_{\mu}$  corresponds to

$$
\left| \tilde {\phi} = D _ {\mu} h _ {\mu} \left(\frac {\partial}{\partial \varepsilon_ {\nu}}\right) = \left(D _ {\mu} h _ {\mu} \left(D _ {\mu} h _ {0}\right) ^ {- 1}\right) (\phi) = D _ {0} \left(\beta \circ \Phi\right) \left(D _ {\mu} R _ {\mu} ^ {- 1} \left(\Lambda (\phi)\right)\right) \right|.
$$

Using identification $\Omega^{-1,1}(\mathbb{D}^*)\simeq A_{\infty}(\mathbb{D})$, provided by the mapping $D_0\beta$, we get

$$
\left. \frac {\partial}{\partial \varepsilon_ {\nu}} \right| _ {\mu} = P \left(D _ {\mu} R _ {\mu} ^ {- 1} (\nu)\right) = P \left(R (\nu , \mu)\right),\tag{1.5}
$$

where

$$
R (\nu , \mu) = \left(\frac {\nu}{1 - | \mu | ^ {2}} \frac {(w _ {\mu}) _ {z}}{(\overline {{w}} _ {\mu}) _ {\bar {z}}}\right) \circ w _ {\mu} ^ {- 1},\tag{1.6}
$$

and $P:L^{\infty}(\mathbb{D}^{*})\to \Omega^{-1,1}(\mathbb{D}^{*})$ is the projection onto the subspace of harmonic Beltrami differentials, defined by the decomposition (1.3). Explicitly,

$$
(P \mu) (z) = \frac {3 (1 - | z | ^ {2}) ^ {2}}{\pi} \iint_ {\mathbb {D} ^ {*}} \frac {\mu (\zeta)}{(1 - \zeta \bar {z}) ^ {4}} d ^ {2} \zeta .\tag{1.7}
$$

REMARK 1.3. Right translating $\nu \in T_0T(1)$ defines a holomorphic tangent vector

$$
D _ {0} R _ {[ \mu ]} (\nu) = (1 - | \mu | ^ {2})   \nu \circ w _ {\mu}   \frac {(\overline {{w}} _ {\mu}) _ {\bar {z}}}{(w _ {\mu}) _ {z}} \in T _ {[ \mu ]} T (1)
$$

at every $[\mu] \in T(1)$. In Bers coordinates on $U_{\mu}$ this tangent vector is represented by $\nu \in \Omega^{-1,1}(\mathbb{D}^*)$. However, the family $\{D_0R_{[\mu]}(\nu)\}_{[\mu] \in T(1)}$ of holomorphic tangent vectors does not form a smooth vector field on $T(1)$ since the left translations are not continuous on $T(1)$.

1.1.5. The universal Teichmüller curve. The universal Teichmüller curve $\mathcal{T}(1)$ is a natural complex fiber space over $T(1)$ with a holomorphic projection map $\pi : \mathcal{T}(1) \to T(1)$. The fiber over each point $[\mu]$ is a quasi-disk $w^{\mu}(\mathbb{D}^{*}) \subset \hat{\mathbb{C}}$ with complex structure induced from $\hat{\mathbb{C}}$ and

$$
\mathcal {T} (1) = \{([ \mu ], z): [ \mu ] \in T (1), z \in w ^ {\mu} (\mathbb {D} ^ {*}) \}.\tag{1.8}
$$

The fibration $\pi : \mathcal{T}(1) \to T(1)$ has a natural holomorphic section given by $T(1) \ni [\mu] \mapsto ([\mu], \infty) \in \mathcal{T}(1)$ — the “zero section”, which defines the embedding $T(1) \hookrightarrow \mathcal{T}(1)$. The universal Teichmüller curve is a complex Banach manifold modeled on $A_{\infty}(\mathbb{D}) \oplus \mathbb{C}^2$, and the mapping

$$
T (1) \times \mathbb {D} ^ {*} \ni ([ \mu ], z) \mapsto ([ \mu ], w ^ {\mu} (z)) \in \mathcal {T} (1)
$$

is a real-analytic isomorphism.

<small><span class="docvortex-page-footnote" data-block-type="page_footnote" style="color:#6b7280">$\hat{C} \setminus \{0\}$</span></small>

<small><span class="docvortex-page-footnote" data-block-type="page_footnote" style="color:#6b7280">$A_{\infty}(\mathbb{D})$</span></small>

<small><span class="docvortex-page-footnote" data-block-type="page_footnote" style="color:#6b7280">$A_{\infty}(\mathbb{D})$</span></small>

<small><span class="docvortex-page-footnote" data-block-type="page_footnote" style="color:#6b7280">$z\mapsto 1 / z$</span></small>

<small><span class="docvortex-page-footnote" data-block-type="page_footnote" style="color:#6b7280">$^{1}$ We identify holomorphic tangent space to  $A_{\infty}(\mathbb{D})$  at every point with  $A_{\infty}(\mathbb{D})$ .</span></small>

<small><span class="docvortex-page-footnote" data-block-type="page_footnote" style="color:#6b7280">$^{2}$ Here  $\hat{C} \setminus \{0\}$  is identified with C via the conformal map  $z \mapsto 1/z$ .</span></small>

<!-- page 20 of 136 -->

1. THE UNIVERSAL TEICHMÜLLER SPACE

11

1.2. Homogeneous spaces of  $\mathrm{Homeo}_{qs}(S^{1})$ . Let  $\mathrm{Homeo}_{qs}(S^{1})$  be the group of orientation preserving quasi-symmetric homeomorphisms of the unit circle  $S^{1}$  (see, e.g., [Leh87] for the definition), and let  $\mathrm{Diff}_{+}(S^{1})$ ,  $\mathrm{Möb}(S^{1})$ , and  $S^{1}$  be the subgroups of  $\mathrm{Homeo}_{qs}(S^{1})$  consisting, respectively, of smooth orientation preserving diffeomorphisms of  $S^{1}$ , of Möbius transformations of  $S^{1}$ , and of rotations of  $S^{1}$ .

Denote by $\mathcal{U}$ the set of univalent functions on $\mathbb{D}$ and let

$\mathcal{D} = \{f\in \mathcal{U}:f(0) = 0,f'(0) = 1,f''(0) = 0,f$ admits a q.c. extension to $\mathbb{C}\}$


> **[ERRATUM W2-02]** (598–617; Lean: `eq_1_9_classD` (Eq19Completed:405)) consequence of W2-01: `𝒟` misses classes whose `f''(0)=0` renormalization has a pole in `𝔻`.

$\widetilde{\mathcal{D}} = \{f\in \mathcal{U}:f(0) = 0,f'(0) = 1,f$ admits a q.c. extension to $\mathbb{C}\}$.

According to the Beurling-Ahlfors extension theorem, the maps

$$
T (1) \ni [ \mu ] \mapsto w ^ {\mu} | _ {\mathbb {D}} \in \mathcal {D}
$$

and

$$
T (1) \ni [ \mu ] \mapsto w _ {\mu} | _ {S ^ {1}} \in \operatorname{Möb} (S ^ {1}) \backslash \operatorname{Homeo} _ {q s} (S ^ {1})
$$

define bijections

$$
\mathcal {D} \stackrel {{\sim}} {{\leftarrow}} T (1) \stackrel {{\sim}} {{\rightarrow}} \operatorname{Mob} (S ^ {1}) \backslash \operatorname{Homeo} _ {q s} (S ^ {1}),\tag{1.9}
$$

which endow the spaces $\mathcal{D}$ and $\mathrm{Möb}(S^1)\backslash\mathrm{Homeo}_{qs}(S^1)$ with the structure of complex Banach manifolds modeled on the Banach space $A_{\infty}(\mathbb{D})$. We will always identify the coset space $\mathrm{Möb}(S^1)\backslash\mathrm{Homeo}_{qs}(S^1)$ with the subgroup of $\mathrm{Homeo}_{qs}(S^1)$ fixing $-1,-i$ and $1$, so that the bijection $T(1)\xrightarrow{\sim}\mathrm{Möb}(S^1)\backslash\mathrm{Homeo}_{qs}(S^1)$ is a group isomorphism.

REMARK 1.4. It is a non-trivial problem to describe the complex Banach manifold structure of the spaces $\mathcal{D}$ and $\mathrm{Möb}(S^1)\backslash \mathrm{Homeo}_{qs}(S^1)$ intrinsically, without using the bijection (1.9).

1.2.1. Conformal welding. According to Beurling-Ahlfors extension theorem, for every $\mathrm{g} \in \mathrm{Möb}(S^1) \backslash \mathrm{Homeo}_{qs}(S^1)$ there exists a unique $\alpha \in \mathrm{Möb}(S^1)$ which fixes 1, and univalent functions $f$ and $g$ on $\mathbb{D}$ and $\mathbb{D}^*$, satisfying the following properties.


> **[ERRATUM W2-03]** (625–640 (CW1–CW3); Lean: `IsWelding`, `conformal_welding`, `welding_of_wA` (S1_2:113, HomogeneousCompleted:41–53)) with W2-01's normalization the Möbius ambiguity `α` disappears; CW3 inherits W2-01's defect.

CW1. $f$ and $g$ admit q.c. extensions to $\mathbb{C}$.

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026for download from IP 130.34.46.51.

CW2. $\alpha \circ \mathrm{g} = (g^{-1}\circ f)|_{S^1}$

CW3. $f(0) = 0$, $f'(0) = 1$, $f''(0) = 0$.

CW4. $g(\infty) = \infty$

The factorization CW2 is known as conformal welding. For $\mathrm{g} = w_{\mu}|_{S^1}$, $[\mu] \in T(1)$, $f = w^{\mu}|_{\mathbb{D}}$ and $g = (w^{\mu} \circ w_{\mu}^{-1} \circ \alpha^{-1})|_{\mathbb{D}^*}$, so that $g(\mathbb{D}^*) = w^{\mu}(\mathbb{D}^*)$. Here $w^{\mu}$ is normalized so that $f$ satisfies CW3 and $\alpha \in \mathrm{Mob}(S^1)$ is uniquely determined by the conditions $\alpha(1) = 1$ and CW4. For $[\mu] \in T(1)$ we will always denote $g_{\mu} = (\alpha \circ w_{\mu})|_{S^1}$, $f^{\mu} = f$ and $g_{\mu} = g$, so that

$$
g _ {\mu} = (g _ {\mu} ^ {- 1} \circ f ^ {\mu}) | _ {S ^ {1}}.
$$

Slightly abusing notations, we will denote by  $g_{\mu}$  a q.c. extension of  $g_{\mu} = (\alpha \circ w_{\mu})|_{S^{1}} \in \mathrm{M}\ddot{\mathrm{o}}\mathrm{b}(S^{1})\backslash\mathrm{Homeo}_{qs}(S^{1})$  given by  $\alpha \circ w_{\mu}$ . Since  $\alpha \in \mathrm{M}\ddot{\mathrm{o}}\mathrm{b}(S^{1})$  fixes 1, the q.c. mapping  $g_{\mu}$  satisfies the reflection property (1.2) and the factorization

$$
g _ {\mu} = g _ {\mu} ^ {- 1} \circ f ^ {\mu},\tag{1.10}
$$

<!-- page 21 of 136 -->

12

1. CURVATURE PROPERTIES AND CHERN FORMS

where $f^{\mu} = w^{\mu}$ and $g_{\mu} = w^{\mu} \circ w_{\mu}^{-1} \circ \alpha^{-1}$. We will distinguish between $\mathrm{g}_{\mu} \in \mathrm{M}\ddot{\mathrm{o}}\mathrm{b}(S^{1})\backslash \mathrm{Homeo}_{qs}(S^{1})$ and its q.c. extension by explicitly specifying either the property CW2 or the factorization (1.10).

The following result will be used in Section 3.

LEMMA 1.5. Let $\mu \in \Omega^{-1,1}(\mathbb{D}^{*})_{1} = \Omega^{-1,1}(\mathbb{D}^{*})\cap L^{\infty}(\mathbb{D}^{*})_{1}$ and $\mathrm{g}_{\mu} = \alpha \circ w_{\mu}$ the q.c. mapping introduced above. Then the mapping $\mathrm{g}_{\mu}$ fixes 0 and $\infty$.


> **[IMPLICIT HYPOTHESIS W2-04]** (658; Lean: `lemma_1_5` (S1_2:164)) TT's content holds for its own normalization; restated for the corrected normalization (`𝗀_μ(0)=0` is false for `α_μ = id`, `w_μ(0) ≠ 0`). Uses of Lemma 1.5 at TT:1618, 1630, 4786 rely on the renormalized form.

PROOF. By the reflection property (1.2) and the factorization (1.10), it is sufficient to prove that $f^{\mu} = w^{\mu}$ fixes $\infty$. Denote


> **[IMPLICIT HYPOTHESIS W2-05]** (660; Lean: `lemma_1_5_fB_infty` (S1_2:182)) same as W2-04 (normalization change; TT's form is the `c = 0` case).

$$
\gamma = \imath \circ \gamma_ {\mu} \circ \imath , \quad g = \imath \circ g _ {\mu} \circ \imath , \quad f = \imath \circ f ^ {\mu} \circ \imath , \quad \imath^ {*} (\mu) = \mu \circ \imath   \frac {\overline {{\imath_ {z}}}}{\imath_ {z}},
$$

where $\iota(z) = z^{-1}$. The factorization (1.10) for $\mathrm{g}_{\mu}$ gives $\mathrm{g} = g^{-1} \circ f$, and the property CW3 for $f^{\mu}$ yields the following Laurent expansion of $f$ at $\infty$,

$$
f (z) = z + \frac {a _ {1}}{z} + \frac {a _ {2}}{z ^ {2}} + \dots .\tag{1.11}
$$

We will prove that $f(0) = 0$ for $\mu \in \Omega^{-1,1}(\mathbb{D}^*)_1$ by exploiting the argument in Royden-Earle's proof of the Ahlfors-Weill theorem, as presented in [Nag88, Sect. 3.8.5].

Namely, $f$ satisfies the Beltrami equation with the Beltrami differential $\nu = \iota^{*}(\mu)|_{\mathbb{D}}$, which is supported on $\mathbb{D}$. The fundamental theorem from the theory of q.c. mappings (see, e.g. [Ahl87]) asserts that $f$ admits the series representation

$$
f (z) = z + P (\nu) (z) + P (\nu H (\nu)) (z) + P (\nu H (\nu H (\nu))) (z) + \dots ,\tag{1.12}
$$

which is uniformly and absolutely convergent on $\mathbb{C}$. Here for $h\in C^2 (\mathbb{D})$ we denote

$$
\begin{array}{l} P (h) (z) = - \frac {1}{\pi} \iint_ {\mathbb {D}} \frac {h (\zeta)}{\zeta - z}   d ^ {2} \zeta , \\ H (h) (z) = - \frac {1}{\pi} \iint_ {\mathbb {D}} \frac {h (\zeta)}{(\zeta - z) ^ {2}}   d ^ {2} \zeta , \end{array}
$$

where the latter integral — the Hilbert transform, is understood in the principal value sense. Since $\nu$ has compact support, it immediately follows from the definition of the operators $P$ and $H$ that the series (1.12) has the Laurent expansion (1.11) at $\infty$. We will prove that for $\nu \in \Omega^{-1,1}(\mathbb{D})$ each term of this series vanishes at $z = 0$. Representing $\nu(z) = -\frac{1}{2}(1 - |z|^2)^2 \sum_{n=0}^{\infty} a_n \bar{z}^n$ and using polar coordinates, we get for any $(n-1)$-iterate of the operator $\nu H$, $n > 1$,

$$
\begin{array}{c} P (\nu H (\nu H (\nu \dots H (\nu)))) (0) \\ = \left(\frac {1}{2 \pi}\right) ^ {n} \iint_ {\mathbb {D}} \dots \iint_ {\mathbb {D}} \frac {\sum_ {m _ {1} , \dots m _ {n}} a _ {m _ {1}} \dots a _ {m _ {n}} r _ {1} ^ {m _ {1} + 1} \dots r _ {n} ^ {m _ {n} + 1} e ^ {- i m _ {1} \theta_ {1}} \dots e ^ {- i m _ {n} \theta_ {n}}}{r _ {1} e ^ {i \theta_ {1}} (r _ {2} e ^ {i \theta_ {2}} - r _ {1} e ^ {i \theta_ {1}}) ^ {2} \dots (r _ {n} e ^ {i \theta_ {n}} - r _ {n - 1} e ^ {i \theta_ {n - 1}}) ^ {2}} \\ (1 - r _ {1} ^ {2}) ^ {2} \dots (1 - r _ {n} ^ {2}) ^ {2} d r _ {1} d \theta_ {1} \dots d r _ {n} d \theta_ {n} \\ = \sum_ {m _ {1}, \dots , m _ {n} = 0} ^ {\infty} a _ {m _ {1}} \dots a _ {m _ {n}} I _ {m _ {1}, \dots , m _ {n}}, \end{array}
$$

where each integral in the definition of $H$ is understood in the principal value sense. The interchange of the orders of summation and integration can be easily justified.

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026for download from IP 130.34.46.51.

<!-- page 22 of 136 -->

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

1. THE UNIVERSAL TEICHMÜLLER SPACE

13

For fixed $r_1 \neq 0, r_1 \neq r_2, r_2 \neq r_3, \ldots, r_{n-1} \neq r_n$, let

$$
\begin{array}{l} I _ {m _ {1}, \dots , m _ {n}} (r _ {1}, \dots , r _ {n}) \\ = \int_ {0} ^ {2 \pi} \dots \int_ {0} ^ {2 \pi} \frac {e ^ {- i m _ {1} \theta_ {1}} \dots e ^ {- i m _ {n} \theta_ {n}} d \theta_ {1} \cdots d \theta_ {n}}{r _ {1} e ^ {i \theta_ {1}} (r _ {2} e ^ {i \theta_ {2}} - r _ {1} e ^ {i \theta_ {1}}) ^ {2} \dots (r _ {n} e ^ {i \theta_ {n}} - r _ {n - 1} e ^ {i \theta_ {n - 1}}) ^ {2}}. \end{array}
$$

A change of variables $\theta_{k}\mapsto \theta_{k} + \theta$, $k = 1,\dots ,n$ gives

$$
I _ {m _ {1}, \dots , m _ {n}} (r _ {1}, \dots , r _ {n}) = e ^ {- i (m _ {1} + \dots + m _ {n} + (2 n - 1)) \theta} I _ {m _ {1}, \dots , m _ {n}} (r _ {1}, \dots , r _ {n}).
$$

Since all $m_{k}\geq 0$ and $2n - 1 > 0$ for $n\geq 1$, we have $e^{-i(m_1 + \ldots +m_n + (2n - 1))^{\theta}}\neq 1$ and hence

$$
I _ {m _ {1}, \dots , m _ {n}} (r _ {1}, \dots , r _ {n}) = 0.
$$

This proves that all $I_{m_1,\dots,m_n}$ vanish. Therefore $f(0) = 0$.

REMARK 1.6. Since $P(f)_z = H(f)$, it also follows from the proof that $f_z(0) = 1$.


> **[IMPLICIT HYPOTHESIS W2-06]** (724; Lean: `remark_1_6` (S1_2:191)) `λ_c`: normalization (W2-01). `dz`: TT's `f_z` is the Wirtinger derivative (f is only q.c. at 0, coefficient `ι^*μ ≠ 0`); our first `deriv` was a junk value (formalization).

Similar to (1.9), there are bijections

$$
\widetilde {\mathcal {D}} \xleftarrow {\sim} \mathcal {T} (1) \xrightarrow {\sim} S ^ {1} \backslash \operatorname{Homeo} _ {q s} (S ^ {1}),
$$

where we always identify the coset space $S^1 \backslash \mathrm{Homeo}_{qs}(S^1)$ with the stabilizer of 1 in $\mathrm{Homeo}_{qs}(S^1)$ (see, e.g., [Teo04]). For every $g \in S^1 \backslash \mathrm{Homeo}_{qs}(S^1)$ there exist unique univalent functions $f$ and $g$ on $\mathbb{D}$ and $\mathbb{D}^*$, satisfying the properties CW1, CW4 and

$\mathbf{CW2^{\prime}}$ $\mathrm{g} = (g^{-1}\circ f)|_{S^1};$

$\mathbf{CW3^{\prime}}$ . $f(0) = 0$ $f^{\prime}(0) = 1$

Namely, the fibration $\pi : \mathcal{T}(1) \longrightarrow T(1)$ is the fiber space $S^1 \backslash \mathrm{Homeo}_{qs}(S^1)$ over $\mathrm{Möb}(S^1) \backslash \mathrm{Homeo}_{qs}(S^1)$ with the fibers isomorphic to $S^1 \backslash \mathrm{Möb}(S^1) \simeq \mathbb{D}^*$. The points in the fiber at $[\mu] \in T(1)$ correspond to the points $\sigma_w \circ g_\mu \in S^1 \backslash \mathrm{Homeo}_{qs}(S^1)$, $w \in \mathbb{D}^*$ with$^3$


> **[IMPLICIT HYPOTHESIS W2-14]** (738, 875; Lean: `sigma_comp` (S1_2:432)) memoir's formula for `c` has a pole: `a = −2, b = 2` gives the identity (`c = ∞`), not covered by the finite formula.

$$
\sigma_ {w} (z) = \frac {1 - w}{1 - \bar {w}} \frac {1 - z \bar {w}}{z - w} \in S ^ {1} \backslash \operatorname{Möb} (S ^ {1}).
$$

Using the properties CW1 and CW2 for $\mathrm{g}_{\mu}$, we get the factorization $\mathbf{CW2}'$ for $\gamma$ is

$$
\mathrm{g} = \sigma_ {w} \circ \mathrm{g} _ {\mu} = (g ^ {- 1} \circ f) | _ {S ^ {1}},
$$

where

$$
f = \lambda_ {w} \circ f ^ {\mu}, \quad g = \lambda_ {w} \circ g _ {\mu} \circ \sigma_ {w} ^ {- 1},
$$

and

$$
\lambda_ {w} (z) = \frac {z}{c _ {w} z + 1}, \quad c _ {w} = - \frac {1}{g _ {\mu} (w)} = - \frac {1}{2} \frac {f ^ {\prime \prime} (0)}{f ^ {\prime} (0)},
$$

so that $(g_{\mu} \circ \sigma_w^{-1})(\infty) = g_{\mu}(w)$, and the functions $f$ and $g$ satisfy the properties $\mathbf{CW3}'$ and $\mathbf{CW4}$ respectively. The mapping

$$
\mathcal {T} (1) \ni ([ \mu ], g _ {\mu} (w)) \mapsto \mathrm{g} = \sigma_ {w} \circ \mathrm{g} _ {\mu} \in S ^ {1} \backslash \mathrm{Homeo} _ {q s} (S ^ {1})
$$

establishes the isomorphism $\mathcal{T}(1)\stackrel {\sim}{\to}S^{1}\backslash \mathrm{Homeo}_{qs}(S^{1})$

As before, we will also denote by $\mathrm{g}$ a q.c. extension of $\mathrm{g} \in S^1 \backslash \mathrm{Homeo}_{qs}(S^1)$ which satisfies the reflection property (1.2) and admits the factorization $\mathrm{g} = g^{-1} \circ f$.

<small><span class="docvortex-page-footnote" data-block-type="page_footnote" style="color:#6b7280">$^{3}$ Here the subscript w does not stand for the derivative.</span></small>

<!-- page 23 of 136 -->

14

1. CURVATURE PROPERTIES AND CHERN FORMS

REMARK 1.7. It is known [Kir87] that $\mathrm{Diff}_{+}(S^{1})$ is an infinite-dimensional Lie group and homogeneous spaces $\mathrm{Möb}(S^1)\backslash \mathrm{Diff}_{+}(S^{1})$ and $S^1\backslash \mathrm{Diff}_{+}(S^{1})$ are infinite-dimensional complex Fréchet manifolds. In this case conformal welding readily follows from the Riemann mapping theorem without using q.c. mappings [Kir87]. Note that our convention for the conformal welding is different from that in [Kir87]: we are using right cosets instead of left cosets.

The bijection $\mathcal{T}(1) \xrightarrow{\sim} S^1 \backslash \mathrm{Homeo}_{qs}(S^1)$ endows the universal Teichmüller curve $\mathcal{T}(1)$ with the group structure. Explicitly,

$$
(\lambda ], z) = ([ \nu ], \zeta) * ([ \mu ], w) ^ {- 1},
$$

where

$$
\lambda = \left(\frac {\nu - \mu}{1 - \bar {\mu} \nu} \frac {\mathrm{g} _ {z}}{\overline {{\mathrm{g}}} _ {\bar {z}}}\right) \circ \mathrm{g} ^ {- 1}\tag{1.13}
$$

and

$$
z = \left(w ^ {\lambda} \circ g \circ (w ^ {\nu}) ^ {- 1}\right) (\zeta).\tag{1.14}
$$

Here $\mathrm{g}$ is a q.c. extension of $\sigma_u \circ \mathrm{g}_\mu$, $u = g_\mu^{-1}(w)$, and the point $([\lambda], z) \in \mathcal{T}(1)$ does not depend on the choice of the extension $\mathrm{g}$.

The mapping

$$
T (1) \ni [ \mu ] \mapsto \gamma_ {\mu} \in S ^ {1} \backslash \mathrm{Homeo} _ {q s} (S ^ {1}) \simeq \mathcal {T} (1)
$$

is a complex-analytic embedding of $T(1)$ into $\mathcal{T}(1)$ which is not a group homomorphism. On the other hand, the natural embedding

$$
\operatorname{Möb} (S ^ {1}) \backslash \operatorname{Homeo} _ {q s} (S ^ {1}) \simeq T (1) \ni [ \mu ] \mapsto w _ {\mu} \in S ^ {1} \backslash \operatorname{Homeo} _ {q s} (S ^ {1}) \simeq \mathcal {T} (1)
$$

is a group homomorphism, though not a complex-analytic mapping. Considering $w_{\mu}$ as an element of $S^1 \backslash \mathrm{Homeo}_{qs}(S^1)$ via this embedding, it admits a conformal welding

$$
w _ {\mu} = \mathrm{g} _ {\mu} ^ {- 1} \circ \mathrm{f} ^ {\mu}\tag{1.15}
$$

that satisfies the properties CW1, CW2', CW3', CW4. In terms of the functions $f^{\mu}$ and $g_{\mu}$ satisfying properties CW1-CW4, we have

$$
\mathrm{f} ^ {\mu} = \lambda_ {\mu} \circ f ^ {\mu} \quad \text {and} \quad \mathrm{g} _ {\mu} = \lambda_ {\mu} \circ g _ {\mu} \circ \alpha_ {\mu} ^ {- 1},
$$

where $\alpha_{\mu}\in \mathrm{PSU}(1,1)$ is such that $w_{\mu} = \alpha_{\mu}\circ \gamma_{\mu}$, and $\lambda_{\mu}\in \mathrm{PSL}(2,\mathbb{C})$ is uniquely determined by the conditions $\mathrm{f}^{\mu}(0) = 0,(\mathrm{f}^{\mu})^{\prime}(0) = 1$ and $\mathrm{g}_{\mu}(\infty) = \infty$.

1.2.2. The horizontal and vertical subspaces. The right translations $R_{([\mu],z)} : \mathcal{T}(1) \to \mathcal{T}(1)$ are biholomorphic automorphisms of $\mathcal{T}(1)$ [Ber73]. The holomorphic tangent space to $\mathcal{T}(1)$ at $([\mu], z)$ is identified with the holomorphic tangent space at $(0, \infty)$ — the origin of $\mathcal{T}(1)$ by

$$
T _ {([ \mu ], z)} \mathcal {T} (1) = D _ {(0, \infty)} R _ {([ \mu ], z)} (T _ {(0, \infty)} \mathcal {T} (1)) \simeq T _ {(0, \infty)} \mathcal {T} (1).
$$

The holomorphic tangent space at the origin naturally splits into the direct sum of horizontal and vertical subspaces,

$$
T _ {(0, \infty)} \mathcal {T} (1) = \Omega^ {- 1, 1} (\mathbb {D} ^ {*}) \oplus \mathbb {C}.
$$

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026for download from IP 130.34.46.51.

The identification of holomorphic tangent spaces provides a natural splitting of the tangent space at every point in  $\mathcal{T}(1)$  into the direct sum of horizontal and vertical subspaces. Lifts of horizontal and vertical tangent vectors at the origin of  $\mathcal{T}(1)$  to every point in the fiber at the origin are explicitly described as follows.

<!-- page 24 of 136 -->

1. THE UNIVERSAL TEICHMÜLLER SPACE

15

TV1. Let $\mu \in \Omega^{-1,1}(\mathbb{D}^*) \subset T_{(0,\infty)}\mathcal{T}(1)$ be a horizontal tangent vector to $\mathcal{T}(1)$ at the origin. A curve $([t\mu], z(t))$, $z(0) = z$, which defines the horizontal lift of $\mu$ to the point $(0,z) \in \mathcal{T}(1)$ in the fiber $\pi^{-1}(0)$ at the origin, for small $t$ is given by the equation

$$
((\mu (t) ], \infty) * (0, z) = ([ t \mu ], z (t)).
$$

Using (1.13), (1.14) and Lemma 1.5, we get

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026for download from IP 130.34.46.51.

$$
\mu (t) = (\sigma_ {z} ^ {- 1}) ^ {*} (t \mu) = t \mu \circ \sigma_ {z} ^ {- 1} \frac {\overline {{(\sigma_ {z} ^ {- 1}) ^ {\prime}}}}{(\sigma_ {z} ^ {- 1}) ^ {\prime}} \quad \text {and} \quad z (t) = w ^ {t \mu} (z).
$$

Thus the horizontal lift of $\mu \in T_{(0,\infty)}\mathcal{T}(1)$ to every point in the fiber $(0,z)\in \pi^{-1}(0)$ is the vector field

$$
\tau_ {\mu} = \left. \frac {\partial}{\partial \varepsilon_ {\mu}} \right| _ {0} + \dot {w} ^ {\mu} (z) \frac {\partial}{\partial z}, \quad \mathrm{where} \quad \dot {w} ^ {\mu} (z) = \frac {d z}{d t} (0)
$$

(cf. [Wol86]). At the point $(0,z)\in \pi^{-1}(0)$ the vector field $\tau_{\mu}$ is identified with the horizontal tangent vector $(\sigma_z^{-1})^*\mu \in T_{(0,\infty)}\mathcal{T}(1)$.

TV2. Let $\mathbf{1} \in \mathbb{C} \subset T_{(0,\infty)}\mathcal{T}(1)$ be the vertical tangent vector to $\mathcal{T}(1)$ at the origin, given by the value of the vector field $\partial_z = \frac{\partial}{\partial z}$ at $z = \infty$. A curve defining the right translate of $\mathbf{1}$ to the point $(0,z) \in \mathcal{T}(1)$ in the fiber $\pi^{-1}(0)$ at the origin for small $t$ is given by the equation

$$
(0, t ^ {- 1}) * (0, z) = (0, z (t)),
$$

and it follows from (1.14) that

$$
\frac {d z}{d t} (0) = \frac {(1 - z) (1 - | z | ^ {2})}{(1 - \bar {z})}.
$$

Thus the right translate of $\mathbf{1} \in T_{(0,\infty)}\mathcal{T}(1)$ to the point $(0,z) \in \pi^{-1}(0)$ is the vector $\frac{(1-z)(1-|z|^2)}{(1-\bar{z})}\partial_z$ at $(0,z)$. As a result, the vector field $\partial_z$ at every point $(0,z) \in \pi^{-1}(0)$ is identified with the vertical tangent vector

$$
\frac {(1 - \bar {z})}{(1 - z) (1 - | z | ^ {2})} \mathbf {1} \in T _ {(0, \infty)} \mathcal {T} (1).
$$

1.2.3. The isomorphisms of the tangent spaces. The real tangent vector space  $T_{0}^{\mathbb{R}} S^{1} \backslash \text{Homeo}_{qs}(S^{1})$  to  $S^{1} \backslash \text{Homeo}_{qs}(S^{1})$  at the origin is identified with the subspace of Zygmund class continuous real-valued vector fields  $u = u(\theta) \frac{d}{d\theta}$  on  $S^{1}$  (see, e.g., [Teo04] for the definition), satisfying

$$
\int_ {0} ^ {2 \pi} u (\theta) d \theta = 0.
$$

In particular, the Fourier series $u(\theta) = \sum_{n\in \mathbb{Z}}c_ne^{in\theta}$ is absolutely convergent. For $|z| = 1$ set

$$
\tilde {u} (z) = i \sum_ {n \in \mathbb {Z} \backslash \{0 \}} c _ {n} z ^ {n + 1}.
$$

The function $\tilde{u}$ on $S^1$ admits the decomposition

$$
\tilde {u} = u _ {+} + u _ {-},
$$

<!-- page 25 of 136 -->

16

1. CURVATURE PROPERTIES AND CHERN FORMS

where $u_{+}$ and $u_{-}$ are boundary values of functions holomorphic on $\mathbb{D}$ and $\mathbb{D}^*$ respectively and $u_{+}(0) = 0$. Explicitly,

$$
\left| u _ {+} (z) = i \sum_ {n = 1} ^ {\infty} c _ {n} z ^ {n + 1}, \right.
$$

$$
\left| u _ {-} (z) = i \sum_ {n = 1} ^ {\infty} c _ {- n} z ^ {1 - n}. \right.
$$

It is a difficult problem to characterize the Zygmund class in terms of the Fourier series (cf. Remark 1.4). On the other side, in terms of the Fourier series the almost complex structure $J$ on $T_0^{\mathbb{R}} S^1 \backslash \mathrm{Homeo}(S^1)$ is explicitly given by the classical conjugation operator

$$
J \mathrm{u} = i \sum_ {n \in \mathbb {Z} \backslash \{0 \}} \operatorname{sgn} (n) c _ {n} e ^ {i n \theta} \frac {d}{d \theta} \quad \text {for} \quad \mathrm{u} = \sum_ {n \in \mathbb {Z} \backslash \{0 \}} c _ {n} e ^ {i n \theta} \frac {d}{d \theta}.
$$

REMARK 1.8. Note that our definition of the operator $J$ differs by a negative sign from the definition in [Kir87, NV90] for the homogeneous space $S^1 \setminus \mathrm{Diff}_+ (S^1)$.

The holomorphic and anti-holomorphic tangent vectors at the origin are

$$
\mathrm{v} = \frac {\mathrm{u} - i J \mathrm{u}}{2} = \sum_ {n = 1} ^ {\infty} c _ {n} e ^ {i n \theta} \frac {d}{d \theta} \quad \text {and} \quad \bar {\mathrm{v}} = \frac {\mathrm{u} + i J \mathrm{u}}{2} = \sum_ {n = - \infty} ^ {- 1} c _ {n} e ^ {i n \theta} \frac {d}{d \theta}.
$$

For every smooth function $\mathcal{F}$ in a neighborhood of the origin in $\mathcal{T}(1)$ and $\mathrm{u} \in T_0^{\mathbb{R}} S^1 \backslash \mathrm{Homeo}_{qs}(S^1)$ set

$$
\dot {\mathcal {F}} [ \mathrm{u} ] = \left. \frac {d}{d t} \right| _ {t = 0} \mathcal {F} (\mathrm{g} ^ {t}),
$$

where  $g_{t}$  is a curve in  $S^{1}\backslash\mathrm{Homeo}_{qs}(S^{1})$  with the tangent vector u at the origin. Corresponding directional derivatives of F at the origin in  $\mathcal{T}(1)$  in the holomorphic and anti-holomorphic directions v and  $\bar{v}$  are defined by

$$
\partial \mathcal {F} (\mathrm{v}) = \frac {1}{2} \left(\dot {\mathcal {F}} [ \mathrm{u} ] - i \dot {\mathcal {F}} [ J \mathrm{u} ]\right), \quad \text {and} \quad \bar {\partial} \mathcal {F} (\bar {\mathrm{v}}) = \frac {1}{2} \left(\dot {\mathcal {F}} [ \mathrm{u} ] + i \dot {\mathcal {F}} [ J \mathrm{u} ]\right).\tag{1.16}
$$

For $s\in \mathbb{R}$ let

$$
\mathcal {H} ^ {s} (S ^ {1}) = \left\{\mathrm{u} = \sum_ {n = - \infty} ^ {\infty} a _ {n} e ^ {i n \theta} \frac {d}{d \theta}: \sum_ {n = - \infty} ^ {\infty} | n | ^ {2 s} | a _ {n} | ^ {2} <   \infty \right\}
$$

be the Sobolev space of complex-valued vector fields on $S^1$. The properties of the tangent spaces $T_0S^1 \backslash \mathrm{Homeo}_{qs}(S^1)$, $T_0\widetilde{\mathcal{D}}$ and $T_0\mathrm{Möb}(S^1)\backslash \mathrm{Homeo}_{qs}(S^1)$, which will be used in Section 5, can be succinctly summarized as follows (see [Teo04] for details).

TS1. Under the $\mathbb{R}$-linear isomorphism $T_0^{\mathbb{R}}S^1\backslash \mathrm{Homeo}_{qs}(S^1)\stackrel {\sim}{\to} T_0\widetilde{\mathcal{D}}$

$$
\left| u (\theta) = \sum_ {n \in \mathbb {Z} \backslash \{0 \}} c _ {n} e ^ {i n \theta} \mapsto u _ {+} (z) = i \sum_ {n = 1} ^ {\infty} c _ {n} z ^ {n + 1}, \right.
$$

and $\dot{f}|_{\mathbb{D}} = u_{+},\dot{g}_{0}|_{\mathbb{D}^{*}} = -u_{-}$, where

$$
\dot {f} = \left. \frac {d}{d t} f ^ {t} \right| _ {t = 0}, \quad \dot {g} = \left. \frac {d}{d t} g _ {t} \right| _ {t = 0},
$$

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

<!-- page 26 of 136 -->

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

1. THE UNIVERSAL TEICHMÜLLER SPACE

17

$\gamma_{t} = g_{t}^{-1}\circ f^{t}$ is a smooth curve in $\mathcal{T}(1)$ tangent to u at the origin, and $\dot{g}_0(z) = \dot{g} (z) - \dot{g}'(\infty)z.$

TS2. Under the $\mathbb{R}$-linear isomorphism

$$
T _ {0} ^ {\mathbb {R}} \operatorname{Möb} (S ^ {1}) \backslash \operatorname{Homeo} _ {q s} (S ^ {1}) \xrightarrow {\sim} T _ {0} T (1) \xrightarrow {D _ {0} \beta} A _ {\infty} (\mathbb {D})
$$

$$
u (\theta) = \sum_ {n \in \mathbb {Z} \backslash \{- 1, 0, 1 \}} c _ {n} e ^ {i n \theta} \mapsto \frac {d ^ {3} u _ {+}}{d z ^ {3}} (z) = i \sum_ {n = 2} ^ {\infty} \left(n ^ {3} - n\right) c _ {n} z ^ {n - 2}.
$$

TS3. If

$$
\phi (z) = \sum_ {n = 2} ^ {\infty} (n ^ {3} - n) a _ {n} z ^ {n - 2} \in A _ {\infty} (\mathbb {D})
$$

then

$$
\left| \sum_ {n = 2} ^ {\infty} n ^ {2 s} | a _ {n} | ^ {2} <   \infty \quad \text {for all} \quad s <   1. \right|
$$

TS4. $T_0^{\mathbb{R}}S^1\backslash \mathrm{Homeo}_{qs}(S^1)\subset \mathcal{H}^s (S^1)$ for all $s < 1$

1.3. Teichmüller spaces and Teichmüller curves of Fuchsian groups. Let $\Gamma$ be a Fuchsian group, i.e., a discrete subgroup of PSU(1,1). Let

$$
L ^ {\infty} (\mathbb {D} ^ {*}, \Gamma) = \left\{\mu \in L ^ {\infty} (\mathbb {D} ^ {*}): \mu \circ \gamma \frac {\overline {{\gamma^ {\prime}}}}{\gamma^ {\prime}} = \mu \quad \text {for all} \quad \gamma \in \Gamma \right\}
$$

be the space of bounded Beltrami differentials for $\Gamma$ and

$$
L ^ {\infty} (\mathbb {D} ^ {*}, \Gamma) _ {1} = L ^ {\infty} (\mathbb {D} ^ {*}) _ {1} \cap L ^ {\infty} (\mathbb {D} ^ {*}, \Gamma)
$$

be the open unit ball in $L^{\infty}(\mathbb{D}^{*},\Gamma)$. The Teichmüller space of the Fuchsian group $\Gamma$ is defined by

$$
T (\Gamma) = L ^ {\infty} \left(\mathbb {D} ^ {*}, \Gamma\right) _ {1} / \sim ,
$$

where the equivalence relation is the same as the one used to define the universal Teichmüller space  $T(1)$  in Section 1.1.1. The Teichmüller space  $T(\Gamma)$  has a natural structure of a complex Banach manifold such that the tangent space at the origin of  $T(\Gamma)$  is identified with the Banach space  $\Omega^{-1,1}(\mathbb{D}^{*},\Gamma)$  of bounded harmonic Beltrami differentials for  $\Gamma$ ,

$$
\Omega^ {- 1, 1} (\mathbb {D} ^ {*}, \Gamma) = \Omega^ {- 1, 1} (\mathbb {D} ^ {*}) \cap L ^ {\infty} (\mathbb {D} ^ {*}, \Gamma).
$$

For every Fuchsian group $\Gamma$ the canonical embedding $T(\Gamma) \hookrightarrow T(1)$ is holomorphic, so that the universal Teichmüller space $T(1)$ contains all the Teichmüller spaces $T(\Gamma)$ as complex submanifolds. The universal Teichmüller space $T(1)$ is the Teichmüller space for the trivial Fuchsian group $\Gamma = \{1\}$.

The inverse image of $T(\Gamma)$ under the projection map $\mathcal{T}(1) \to T(\Gamma)$ is called the Bers fiber space $\mathcal{BF}(\Gamma)$. The quasi-Fuchsian group $\Gamma^{\mu} = w^{\mu} \circ \Gamma \circ (w^{\mu})^{-1}$ acts on the fiber $w^{\mu}(\mathbb{D}^{*})$ at the point $[\mu] \in T(\Gamma)$. The Teichmüller curve $\mathcal{T}(\Gamma)$ of the Fuchsian group $\Gamma$ is a fiber space over $T(\Gamma)$ with the fiber $\Gamma^{\mu} \backslash w^{\mu}(\mathbb{D}^{*})$ at the point $[\mu] \in T(\Gamma)$.

The domain $\mathbb{D}^*$ is a model of the hyperbolic plane $\mathbb{H}^2$. The hyperbolic (Poincaré) metric on $\mathbb{D}^*$ — a Hermitian metric of constant Gaussian curvature $-1$, is

$$
d s ^ {2} = \rho (z) | d z | ^ {2} = \frac {4 | d z | ^ {2}}{(1 - | z | ^ {2}) ^ {2}},\tag{1.17}
$$

<!-- page 27 of 136 -->

18

1. CURVATURE PROPERTIES AND CHERN FORMS

and the hyperbolic area 2-form is $\rho(z) d^2 z$. The Fuchsian group $\Gamma$ is of finite type (cofinite) if the corresponding Riemann surface — the orbifold $\Gamma \backslash \mathbb{D}^*$, has a finite hyperbolic area. In this case, the Teichmüller space $T(\Gamma)$ is a finite-dimensional complex manifold with a natural Hermitian metric, called the Weil-Petersson metric. It is defined as Petersson's inner product on tangent spaces $T_{[\mu]} T(\Gamma) \simeq \Omega^{-1,1}(\mathbb{D}^*, \Gamma_\mu)$, where $[\mu] \in T(\Gamma)$ and $\Gamma_\mu = w_\mu \circ \Gamma \circ w_\mu^{-1}$. For $\mu, \nu \in T_0 T(\Gamma)$,

$$
\left\langle \mu , \nu \right\rangle_ {W P} = \iint_ {\Gamma \backslash \mathbb {D} ^ {*}} \mu \bar {\nu} \rho (z) d ^ {2} z.
$$

The Weil-Petersson metric on $T(\Gamma)$ is a Kähler metric.

The following result, due to Patterson [Pat75], will be used in Section 8. Here we present it in a convenient form as in [Teo04].

LEMMA 1.9. Let $\Gamma$ be a cofinite Fuchsian group and $h\in L^{\infty}(\mathbb{D}^{*},\rho (z)d^{2}z)$ be $\Gamma$-automorphic, i.e., $h\circ \gamma = h$ for all $\gamma \in \Gamma$. Then

$$
\iint_ {\Gamma \backslash \mathbb {D} ^ {*}} h (z) \rho (z) d ^ {2} z = \lim _ {r \to 1 ^ {+}} \frac {A (\Gamma \backslash \mathbb {D} ^ {*})}{A (\mathbb {D} _ {r} ^ {*})} \iint_ {\mathbb {D} _ {r} ^ {*}} h (z) \rho (z) d ^ {2} z,
$$

where $\mathbb{D}_r^* = \{z\in \mathbb{D}^* :|z|\geq r\}$, $A(\Gamma \backslash \mathbb{D}^*)$ is the hyperbolic area of the Riemann surface $\Gamma \backslash \mathbb{D}^*$, and $A(\mathbb{D}_r^*)$ is the hyperbolic area of $\mathbb{D}_r^*$.

## 1.4. Resolvent kernel. Let

$$
\Delta_ {0} = - \rho (z) ^ {- 1} \partial_ {z} \partial_ \bar {z}\tag{1.18}
$$

be the Laplace-Beltrami operator of the hyperbolic metric on $\mathbb{D}$, acting on functions. It is well-known (see, e.g., [Hej76, Lan85]) that the differential expression (1.18) defines a unique positive, self-adjoint operator on the Hilbert space $L^2 (\mathbb{D},\rho (z)d^2 z)$, which we still denote by $\Delta_0$. Let

$$
G = \frac {1}{2} \left(\Delta_ {0} + \frac {1}{2}\right) ^ {- 1}
$$

be (a one-half of) the resolvent of $\Delta_0$ at the regular point $\lambda = -\frac{1}{2}$.

REMARK 1.10. Note that the Laplace-Beltrami operator in [Hej76, Lan85] is $4\Delta_0$, so that the regular point $\lambda = -\frac{1}{2}$ for the operator $\Delta_0$ corresponds to $\lambda = -2$ for the Laplace-Beltrami operator in [Hej76, Lan85].

The resolvent $G$ is a bounded integral operator on $L^2 (\mathbb{D},\rho (z)d^2 z)$ with kernel

$$
G (z, w) = \frac {2 u + 1}{2 \pi} \log \frac {u + 1}{u} - \frac {1}{\pi},\tag{1.19}
$$

where $u(z,w)$ is a point-pair invariant on $\mathbb{D}$,

$$
u (z, w) = \frac {| z - w | ^ {2}}{(1 - | z | ^ {2}) (1 - | w | ^ {2})}.
$$

The resolvent kernel $G(z, w)$ has the following properties (see, e.g., [Hej76] and [Lan85, Sect. XIV.3]).

RK1. $G$ is symmetric, $G(z,w) = G(w,z)$, and is a point-pair invariant,

$$
G (\gamma z, \gamma w) = G (z, w) \text {for all} \gamma \in \mathrm{PSU} (1, 1).
$$

RK2. $G(z,w)$ is positive for all $z,w\in \mathbb{D}$.

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026for download from IP 130.34.46.51.

<!-- page 28 of 136 -->

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026for download from IP 130.34.46.51.

1. THE UNIVERSAL TEICHMÜLLER SPACE

19

RK3. If $g \in BC^{\infty}(\mathbb{D})$ — the space of smooth bounded functions on $\mathbb{D}$, then the integral

$$
f (z) = \iint_ {\mathbb {D}} G (z, w) g (w) \rho (w) d ^ {2} w
$$

is absolutely convergent for all $z \in \mathbb{D}$ and $f = G(g) \in BC^{\infty}(\mathbb{D})$ satisfies the differential equation

$$
2 \left(\Delta_ {0} + \frac {1}{2}\right) (f) = g.
$$

Conversely, if $f \in BC^{\infty}(\mathbb{D})$ and $g = 2\left(\Delta_0 + \frac{1}{2}\right)(f) \in BC^{\infty}(\mathbb{D})$, then $f = G(g)$.

RK4. For all $z \in \mathbb{D}$,

$$
\iint_ {\mathbb {D}} G (z, w) \rho (w) d ^ {2} w = 1.
$$

The last property immediately follows from RK3 since

$$
2 \left(\Delta_ {0} + \frac {1}{2}\right) (1) = 1,
$$

where 1 is the constant function equal to 1 on $\mathbb{D}$.

The resolvent kernel $G$ of the Laplace-Beltrami operator on $\mathbb{D}^*$ is given by the same formula (1.19) and satisfies the properties RK1 - RK4.

When $\Gamma$ is a cofinite Fuchsian group, we denote by $G_{\Gamma}$ the one-half of the resolvent of the Laplace-Beltrami operator on the Riemann surface $\Gamma \backslash \mathbb{D}$ at $\lambda = -\frac{1}{2}$. It is a bounded integral operator on $L^2 (\Gamma \backslash \mathbb{D},\rho (z)d^2 z)$ with kernel

$$
G _ {\Gamma} (z, w) = \sum_ {\gamma \in \Gamma} G (z, \gamma w), z, w \in \mathbb {D},\tag{1.20}
$$

and it enjoys all the properties RK1-RK4. The corresponding resolvent kernel on $\Gamma \backslash \mathbb{D}^*$ is given by the same formula with $z, w \in \mathbb{D}^*$.

REMARK 1.11. The operator $G_{\Gamma}$ plays a prominent role in the Weil-Petersson geometry of the finite-dimensional Teichmüller space $T(\Gamma)$ [Wol86].

1.5. Variational formulas. Here we collect necessary variational formulas. To simplify the computations in the following sections, we will use different realizations of the hyperbolic plane $\mathbb{H}^2$, given either by the unit disk $\mathbb{D}$ or its exterior $\mathbb{D}^*$, or by the upper half-plane $\mathbb{U}$.

Let $l$ and $m$ be integers and $\Gamma$ a Fuchsian group (we will be primarily interested in the cases when $\Gamma = \{1\}$, i.e., is a trivial group, and when $\Gamma$ is a cofinite Fuchsian group). Using the model $\mathbb{H}^2 \simeq \mathbb{D}$, tensor of type $(l, m)$ for $\Gamma$ is a $C^\infty$-function $\omega$ on $\mathbb{D}$ satisfying

$$
\omega (\gamma z) \gamma^ {\prime} (z) ^ {l} \overline {{\gamma^ {\prime} (z)}} ^ {m} = \gamma (z) \text {for all} \gamma \in \Gamma .
$$

Let $\omega^{\varepsilon}$ be a smooth family of tensors of type $(l,m)$ for $\Gamma_{\varepsilon \mu} = w_{\varepsilon \mu}\circ \Gamma \circ w_{\varepsilon \mu}^{-1}$, where $\mu \in \Omega^{-1,1}(\mathbb{D},\Gamma)$ and $\varepsilon \in \mathbb{C}$ is sufficiently small. Set

$$
(w _ {\varepsilon \mu}) ^ {*} (\omega^ {\varepsilon}) = \omega^ {\varepsilon} \circ w _ {\varepsilon \mu} ((w _ {\varepsilon \mu}) _ {z}) ^ {l} ((\overline {{w}} _ {\varepsilon \mu}) _ {z}) ^ {m},
$$


> **[ERRATUM 3-01]** (TT:1163; Lean: `pullbackTensor` (S1_5)) OCR/print error: the subscript must be `z̄` (as (6.1) `w^*ρ = ρ∘w \| w_z \| ²`, TT:2563, requires); `(w̄)_z = \overline{w_{z̄}}` would give the wrong tensor

which is a tensor of type $(l,m)$ for $\Gamma$ — a pull-back of the tensor $\omega^{\varepsilon}$ by $w_{\varepsilon \mu}$. Lie derivatives of the family $\omega^{\varepsilon}$ along vector fields $\partial/\partial\varepsilon_{\mu}$ and $\partial/\partial\bar{\varepsilon}_{\mu}$ are defined in the standard way,

$$
L _ {\mu} \omega = \frac {\partial}{\partial \varepsilon} \Big | _ {\varepsilon = 0} (w _ {\varepsilon \mu}) ^ {*} (\omega^ {\varepsilon}) \quad \mathrm{and} \quad L _ {\bar {\mu}} \omega = \frac {\partial}{\partial \bar {\varepsilon}} \Big | _ {\varepsilon = 0} (w _ {\varepsilon \mu}) ^ {*} (\omega^ {\varepsilon}).
$$

<!-- page 29 of 136 -->

20

1. CURVATURE PROPERTIES AND CHERN FORMS

When $\omega$ is a function on $T(\Gamma)$ — a tensor of type $(0,0)$, the Lie derivatives reduce to directional derivatives

$$
L _ {\mu} \omega = \partial \omega (\mu) \quad \text {and} \quad L _ {\bar {\mu}} \omega = \bar {\partial} \omega (\bar {\mu})
$$

— the evaluation of the 1-forms $\partial\omega$ and $\bar{\partial}\omega$ on the holomorphic and antiholomorphic tangent vectors $\mu$ and $\bar{\mu}$ to $T(\Gamma)$ at the origin. Corresponding real vector fields $\frac{\partial}{\partial t_{\mu}}$ are defined by

$$
\frac {\partial}{\partial t _ {\mu}} = \frac {\partial}{\partial \varepsilon_ {\mu}} + \frac {\partial}{\partial \bar {\varepsilon} _ {\mu}},
$$

so that

$$
\frac {\partial}{\partial \varepsilon_ {\mu}} = \frac {1}{2} \left(\frac {\partial}{\partial t _ {\mu}} - i \frac {\partial}{\partial t _ {i \mu}}\right) \quad \text {and} \quad \frac {\partial}{\partial \bar {\varepsilon} _ {\mu}} = \frac {1}{2} \left(\frac {\partial}{\partial t _ {\mu}} + i \frac {\partial}{\partial t _ {i \mu}}\right).
$$

For the model $\mathbb{H}^2\simeq \mathbb{U}$ we have

$$
\left| \frac {\partial}{\partial \varepsilon} w _ {\varepsilon \mu} (z) = - \frac {1}{\pi} \iint_ {\mathbb {U}} R \left(w _ {\varepsilon \mu} (z), w _ {\varepsilon \mu} (u)\right) \mu (u) \left(w _ {\varepsilon \mu}\right) _ {u} ^ {2} (u) d ^ {2} u, \right.\tag{1.21}
$$

$$
\frac {\partial}{\partial \bar {\varepsilon}} w _ {\varepsilon \mu} (z) = - \frac {1}{\pi} \iint_ {\mathbb {U}} R \left(w _ {\varepsilon \mu} (z), \overline {{w _ {\varepsilon \mu} (u)}}\right) \overline {{\mu (u) (w _ {\varepsilon \mu}) _ {u} ^ {2} (u)}} d ^ {2} u,
$$

where the q.c. mapping $w_{\varepsilon \mu}$ is normalized by fixing $0,1,\infty$ and the kernel $R$ is

$$
R (z, u) = \frac {z (z - 1)}{(u - z) u (u - 1)} = \frac {1}{u - z} + \frac {z - 1}{u} - \frac {z}{u - 1}.
$$

Setting

$$
F [ \mu ] = \left. \frac {\partial}{\partial \varepsilon} \right| _ {\varepsilon = 0} w _ {\varepsilon \mu} \quad \text {and} \quad \Phi [ \mu ] = \left. \frac {\partial}{\partial \bar {\varepsilon}} \right| _ {\varepsilon = 0} w _ {\varepsilon \mu},
$$

we get from (1.21)

$$
F [ \mu ] (z) = - \frac {1}{\pi} \iint_ {\mathbb {U}} R (z, u) \mu (u) d ^ {2} u,\tag{1.22}
$$

$$
\Phi [ \mu ] (z) = - \frac {1}{\pi} \iint_ {\mathbb {U}} R (z, \bar {u}) \overline {{\mu (u)}} d ^ {2} u.
$$

The function $\Phi[\mu](z)$ is holomorphic on $\mathbb{U}$ and satisfies

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026for download from IP 130.34.46.51.

$$
\Phi [ \mu ] _ {z z z} (z) = - \frac {6}{\pi} \iint_ {\mathbb {U}} \frac {\overline {{\mu (u)}}}{(\bar {u} - z) ^ {4}} d ^ {2} u.
$$

As it follows from (1.7), the projection $P:L^{\infty}(\mathbb{U})\to \Omega^{-1,1}(\mathbb{U})$ is given by

$$
(P \mu) (z) = - \frac {3 (z - \bar {z}) ^ {2}}{\pi} \iint_ {\mathbb {U}} \frac {\mu (u)}{(u - \bar {z}) ^ {4}} d ^ {2} u.\tag{1.23}
$$

Equivalently, for $\mu(z) = \frac{(z - \bar{z})^2}{2}\overline{\phi(z)}$ with $\phi \in A_{\infty}(\mathbb{U})$, $\Phi[\mu]_{zzz} = \phi$ on $\mathbb{U}$. The function $F[\mu]$ satisfies $F[\mu]_{\bar{z}} = \mu$ on $\mathbb{U}$, and is holomorphic on the lower half-plane $\overline{\mathbb{U}}$.

<!-- page 30 of 136 -->

1. THE UNIVERSAL TEICHMÜLLER SPACE

21

LEMMA 1.12. For $\mu \in \Omega^{-1,1}(\mathbb{U})$ and $z\in \mathbb{U}$,

$$
\lim _ {\varepsilon \to 0} \iint_ {\mathbb {U} (z, \varepsilon)} \frac {\mu (u)}{(u - z) ^ {4}} d ^ {2} u = \lim _ {\varepsilon \to 0} \iint_ {\mathbb {U} (z, \varepsilon)} \frac {\mu (u)}{(u - z) ^ {5}} d ^ {2} u = 0,
$$

where $\mathbb{U}(z,\varepsilon) = \mathbb{U}\setminus \{u\in \mathbb{U}:|u - z| <   \varepsilon \} .$

PROOF. The proof of the first formula essentially follows the classical Ahlfors' proof in [Ahl87, Lemma 2 in Sect. VI D] by using $\mu(u) = \frac{(u - \bar{u})^2}{2}\overline{\phi(u)}$ with $\phi \in A_{\infty}(\mathbb{U})$, the identity

$$
\frac {(u - \bar {u}) ^ {2}}{(u - z) ^ {4}} = \frac {\partial}{\partial u} \left(- \frac {1}{u - z} + \frac {\bar {u} - z}{(u - z) ^ {2}} - \frac {1}{3} \frac {(\bar {u} - z) ^ {2}}{(u - z) ^ {3}}\right),
$$

and Stokes' theorem. The second formula is proved similarly.

Another classical result of Ahlfors [Ahl61] is the following.

LEMMA 1.13. For $\mu \in \Omega^{-1,1}(\mathbb{U})$ and $z\in \mathbb{U}$,

$$
F [ \mu ] (z) = \frac {(z - \bar {z}) ^ {2}}{2} \overline {{\Phi^ {\prime \prime} (z)}} + (z - \bar {z}) \overline {{\Phi^ {\prime} (z)}} + \overline {{\Phi (z)}},
$$

where $\Phi (z) = \Phi [\mu ](z)$

REMARK 1.14. It follows from Lemma 1.13 that $F[\mu]_{zzz} = 0$ for $\mu \in \Omega^{-1,1}(\mathbb{U})$, in agreement with Lemma 1.12.

COROLLARY 1.15. For $\mu \in \Omega^{-1,1}(\mathbb{U})$ and $z\in \mathbb{U}$,

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

$$
\iint_ {\mathbb {U}} \frac {\mu (u)}{(u - z) (u - \bar {z}) ^ {3}} d ^ {2} u = 0.
$$

PROOF. Using (1.22), we have

$$
\begin{array}{c} F [ \mu ] (z) - \frac {(z - \bar {z}) ^ {2}}{2} \overline {{\Phi^ {\prime \prime} (z)}} - (z - \bar {z}) \overline {{\Phi^ {\prime} (z)}} - \overline {{\Phi (z)}} \\ = - \frac {1}{\pi} \iint_ {\mathbb {U}} \mu (u) \frac {(z - \bar {z}) ^ {3}}{(u - z) (u - \bar {z}) ^ {3}} d ^ {2} w. \end{array}
$$

For $\mu \in L^{\infty}(\mathbb{U})_{1}$ set

$$
K _ {\mu} (u, v) = \frac {(w _ {\mu}) _ {u} (u) (w _ {\mu}) _ {v} (v)}{(w _ {\mu} (u) - w _ {\mu} (v)) ^ {2}} \quad \text {and} \quad K _ {\mu} (u, \bar {v}) = \frac {(w _ {\mu}) _ {u} (u) \overline {{(w _ {\mu}) _ {v} (v)}}}{(w _ {\mu} (u) - \overline {{w _ {\mu} (v)}}) ^ {2}}.
$$

We have from (1.21) the following formulas [Ahl62]

$$
\left| \frac {\partial}{\partial \varepsilon} K _ {\varepsilon \mu} (z, u) = - \frac {1}{\pi} \iint_ {\mathbb {I I}} \mu (v) K _ {\varepsilon \mu} (z, v) K _ {\varepsilon \mu} (v, u) d ^ {2} v, \right.\tag{1.24}
$$


> **[IMPLICIT HYPOTHESIS 3-03]** (TT:1301–1320; Lean: `eq_1_24`, `eq_1_25` (Eq124General, relocated from S1_5)) for merely measurable `μ`, `(w_{εμ})_z` at a fixed point and the PV need not exist; TT only applies it to harmonic (smooth) `μ`

$$
\frac {\partial}{\partial \bar {\varepsilon}} K _ {\varepsilon \mu} (z, u) = - \frac {1}{\pi} \iint_ {\mathbb {U}} \overline {{\mu (v)}} K _ {\varepsilon \mu} (z, \bar {v}) K _ {\varepsilon \mu} (\bar {v}, u) d ^ {2} v,
$$

<!-- page 31 of 136 -->

22

1. CURVATURE PROPERTIES AND CHERN FORMS

and

$$
\begin{array}{r l} & {\frac {\partial}{\partial \varepsilon} K _ {\varepsilon \mu} (z, \bar {u}) = - \frac {1}{\pi} \iint_ {\mathbb {U}} \mu (v) K _ {\varepsilon \mu} (z, v) K _ {\varepsilon \mu} (v, \bar {u}) d ^ {2} v,} \\ & {\frac {\partial}{\partial \bar {\varepsilon}} K _ {\varepsilon \mu} (z, \bar {u}) = - \frac {1}{\pi} \iint_ {\mathbb {U}} \overline {{\mu (v)}} K _ {\varepsilon \mu} (z, \bar {v}) K _ {\varepsilon \mu} (\bar {v}, \bar {u}) d ^ {2} v,} \end{array}\tag{1.25}
$$

where the integrals are understood in the principal value sense.

For the model $\mathbb{H}^2\simeq \mathbb{D}$ the q.c. mapping $w_{\mu}$ is normalized by fixing $-1, - i, 1$. The kernel $R$ is given by

$$
R (z, u) = \frac {(z + 1) (z + i) (z - 1)}{(u - z) (u + 1) (u + i) (u - 1)},
$$

and formulas similar to (1.22) hold for $F$ and $\Phi$. In particular, let $f$ be a q.c. mapping such that $f|_{\mathbb{D}} \in \mathcal{D}$, and let $\mu$ be a Beltrami differential supported on the quasi-disk $\Omega^{*} = f(\mathbb{D}^{*})$. Let $v_{t\mu}$ be the solution on $\mathbb{C}$ of the Beltrami equation

$$
(v _ {t \mu}) _ {\bar {z}} = t \mu (v _ {t \mu}) _ {z},
$$

satisfying $v_{t\mu}(0) = 0, v_{t\mu}'(0) = 1$ and $v_{t\mu}''(0) = 0$. Then

$$
\dot {v} = \left. \frac {d}{d t} \right| _ {t = 0} v _ {t \mu}
$$

is a holomorphic function on $\Omega = f(\mathbb{D})$ and

$$
\dot {v} _ {z z z} (z) = - \frac {6}{\pi} \iint_ {\Omega^ {*}} \frac {\mu (u)}{(u - z) ^ {4}} d ^ {2} u.\tag{1.26}
$$

## 2. $T(1)$ as a Hilbert manifold

In this section we are going to endow $T(1)$ with a structure of a complex manifold modeled on the separable Hilbert space

$$
A _ {2} (\mathbb {D}) = \left\{\phi \text {holomorphic on} \mathbb {D}: \| \phi \| _ {2} ^ {2} = \iint_ {\mathbb {D}} | \phi | ^ {2} \rho^ {- 1} (z) d ^ {2} z <   \infty \right\}
$$

of holomorphic functions on $\mathbb{D}$. In the corresponding topology, the universal Teichmüller space $T(1)$ is a disjoint union of uncountably many components on which the right translations act transitively.

## 2.1. Hilbert space structure on tangent spaces. Let

$$
A _ {2} (\mathbb {D} ^ {*}) = \left\{\phi \text {holomorphic on} \mathbb {D} ^ {*}: \| \phi \| _ {2} ^ {2} = \iint_ {\mathbb {D} ^ {*}} | \phi | ^ {2} \rho^ {- 1} (z) d ^ {2} z <   \infty \right\}
$$

be the Hilbert space of holomorphic functions on $\mathbb{D}^*$.

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026for download from IP 130.34.46.51.

LEMMA 2.1. The vector spaces $A_2(\mathbb{D})$ and $A_2(\mathbb{D}^*)$ are subspaces of $A_{\infty}(\mathbb{D})$ and $A_{\infty}(\mathbb{D}^*)$ respectively. The natural inclusion maps $A_2(\mathbb{D}) \hookrightarrow A_{\infty}(\mathbb{D})$ and $A_2(\mathbb{D}^*) \hookrightarrow A_{\infty}(\mathbb{D}^*)$ are bounded linear mappings of Banach spaces.

<!-- page 32 of 136 -->

2. $T(1)$ AS A HILBERT MANIFOLD

23

PROOF. It is sufficient to consider only the spaces of holomorphic functions on $\mathbb{D}$. For every $\phi \in A_2(\mathbb{D})$, let $\phi = \sum_{n=2}^{\infty}(n^3 - n)a_n z^{n-2}$ be the power series expansion. Then

$$
\| \phi \| _ {2} ^ {2} = \iint_ {\mathbb {D}} | \phi | ^ {2} \rho^ {- 1} d ^ {2} z = \frac {\pi}{2} \sum_ {n = 2} ^ {\infty} (n ^ {3} - n) | a _ {n} | ^ {2},
$$

and by Cauchy-Schwarz inequality,

$$
\begin{array}{l} | \phi (z) | = \left| \sum_ {n = 2} ^ {\infty} (n ^ {3} - n) a _ {n} z ^ {n - 2} \right| \\ \qquad \leq \left(\sum_ {n = 2} ^ {\infty} (n ^ {3} - n) | a _ {n} | ^ {2}\right) ^ {1 / 2} \left(\sum_ {n = 2} ^ {\infty} (n ^ {3} - n) | z | ^ {2 n - 4}\right) ^ {1 / 2} \end{array}
$$

for every $z\in \mathbb{D}$ . Since

$$
\sum_ {n = 2} ^ {\infty} (n ^ {3} - n) | z | ^ {2 n - 4} = \frac {6}{(1 - | z | ^ {2}) ^ {4}},
$$

we have

$$
\| \phi \| _ {\infty} = \sup _ {z \in \mathbb {D}} \left| (1 - | z | ^ {2}) ^ {2} \phi (z) \right| \leq \sqrt {\frac {1 2}{\pi}} \| \phi \| _ {2}.
$$

Let

$$
H ^ {- 1, 1} (\mathbb {D}) = \left\{\mu = \rho^ {- 1} \bar {\phi}, \phi \text {holomorphic on} \mathbb {D}: \| \mu \| _ {2} ^ {2} = \iint_ {\mathbb {D}} | \mu | ^ {2} \rho (z) d ^ {2} z <   \infty \right\}
$$

and

$$
H ^ {- 1, 1} (\mathbb {D} ^ {*}) = \left\{\mu = \rho^ {- 1} \bar {\phi}, \phi \text {holomorphic on} \mathbb {D} ^ {*}: \| \mu \| _ {2} ^ {2} = \iint_ {\mathbb {D} ^ {*}} | \mu | ^ {2} \rho (z) d ^ {2} z <   \infty \right\}
$$

be the Hilbert spaces of harmonic Beltrami differentials on $\mathbb{D}$ and $\mathbb{D}^*$ respectively. It follows from Lemma 2.1 that the natural inclusion maps $H^{-1,1}(\mathbb{D})\hookrightarrow \Omega^{-1,1}(\mathbb{D})$ and $H^{-1,1}(\mathbb{D}^{*})\hookrightarrow \Omega^{-1,1}(\mathbb{D}^{*})$ are bounded and under the linear mapping $D_0\beta$, $H^{-1,1}(\mathbb{D}^{*})\stackrel {\sim}{\to}A_{2}(\mathbb{D})$.

REMARK 2.2. It follows from the proof of Lemma 2.1 that every $\mu \in H^{-1,1}(\mathbb{D})$ (respectively in $H^{-1,1}(\mathbb{D}^*)$) satisfies

$$
\lim _ {| z | \to 1} \mu (z) = 0.
$$

Indeed, for given $\varepsilon > 0$ let $N$ be such that

$$
\left| \sum_ {n = N} ^ {\infty} (n ^ {3} - n) | a _ {n} | ^ {2} <   \varepsilon . \right|
$$

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

<!-- page 33 of 136 -->

24

1. CURVATURE PROPERTIES AND CHERN FORMS

Then

$$
\begin{array}{l} | \mu (z) | \leq \frac {(1 - | z | ^ {2}) ^ {2}}{4} \left| \sum_ {n = 2} ^ {N - 1} (n ^ {3} - n) a _ {n} z ^ {n - 2} \right| \\ \qquad + \frac {(1 - | z | ^ {2}) ^ {2}}{4} \left(\sum_ {n = N} ^ {\infty} (n ^ {3} - n) | a _ {n} | ^ {2}\right) ^ {1 / 2} \left(\sum_ {n = 2} ^ {\infty} (n ^ {3} - n) | z | ^ {2 n - 4}\right) ^ {1 / 2} \\ \qquad \leq \frac {(1 - | z | ^ {2}) ^ {2}}{4} \left| \sum_ {n = 2} ^ {N - 1} (n ^ {3} - n) a _ {n} z ^ {n - 2} \right| + \frac {\sqrt {6 \varepsilon}}{4}, \end{array}
$$

so that

$$
\operatorname * {l i m s u p} _ {| z | \to 1} | \mu (z) | \leq \frac {\sqrt {6 \varepsilon}}{4}.
$$

Since $\varepsilon$ is arbitrary this proves the assertion.

For every $[\mu] \in T(1)$ let $D_0R_{[\mu]}\left(H^{-1,1}(\mathbb{D}^*)\right)$ be the subspace of the tangent space $T_{[\mu]}T(1) = D_0R_{[\mu]}\left(\Omega^{-1,1}(\mathbb{D}^*)\right)$ with a Hilbert space structure isomorphic to $H^{-1,1}(\mathbb{D}^*)$. Let $\mathfrak{D}_T$ be the distribution on $T(1)$, defined by the assignment

$$
T (1) \ni [ \mu ] \mapsto D _ {0} R _ {[ \mu ]} \left(H ^ {- 1, 1} (\mathbb {D} ^ {*})\right) \subset T _ {[ \mu ]} T (1).
$$

Similarly, let $\mathfrak{D}_A$ be the distribution on $A_{\infty}(\mathbb{D})$, defined by

$$
A _ {\infty} (\mathbb {D}) \ni \phi \mapsto A _ {2} (\mathbb {D}) \subset T _ {\phi} A _ {\infty} (\mathbb {D}) \simeq A _ {\infty} (\mathbb {D}).
$$

The next statement asserts that under the Bers embedding $\beta : T(1) \to A_{\infty}(\mathbb{D})$ the distribution $\mathfrak{D}_T$ is isomorphic to the restriction of the distribution $\mathfrak{D}_A$ to $\beta(T(1))$.

THEOREM 2.3. For every $[\mu] \in T(1)$ the linear mapping

$$
D _ {0} \left(\beta \circ R _ {[ \mu ]}\right): H ^ {- 1, 1} (\mathbb {D} ^ {*}) \to A _ {2} (\mathbb {D})
$$

is a topological isomorphism.

PROOF. Let $\nu \in H^{-1,1}(\mathbb{D}^*)$. Set $w_{t} = w_{t\nu*\mu} = w_{t\nu} \circ w_{\mu}$ and let $w_{t} = \mathrm{g}_{t}^{-1} \circ \mathrm{f}^{t}$ be the conformal welding associated with the q.c. mapping $w_{t}$ by (1.15). Let $v_{t} = \mathrm{f}^{t} \circ \mathrm{f}^{-1}$, where $w_{\mu} = \mathrm{g}^{-1} \circ \mathrm{f}$ is the factorization for $w_{\mu}$, and set $\Omega = \mathrm{f}(\mathbb{D}) = \mathrm{g}(\mathbb{D})$, $\Omega^{*} = \mathrm{f}(\mathbb{D}^{*}) = \mathrm{g}(\mathbb{D}^{*})$. Since

$$
\beta ([ t \nu * \mu ]) = \mathcal {S} (f ^ {t}) = \mathcal {S} (v _ {t}) \circ f   f _ {z} ^ {2} + \mathcal {S} (f),
$$

we have

$$
D _ {0} \left(\beta \circ R _ {[ \mu ]}\right) (\nu) = \frac {d}{d t} \Big | _ {t = 0} \mathcal {S} (\mathrm{f} ^ {t}) = \dot {v} _ {z z z} \circ \mathrm{ff} _ {z} ^ {2}, \quad \text {where} \quad \dot {v} = \frac {d}{d t} \Big | _ {t = 0} v _ {t}.
$$

The q.c. mapping $v_{t}$ is holomorphic on $\Omega$ and satisfies $v_{t} \circ \mathrm{g} = \mathrm{g}_{t} \circ w_{t\nu}$. Since $\mathrm{g}_t$ and $\mathrm{g}$ are holomorphic on $\mathbb{D}^*$, the Beltrami differential of $v_{t}$ is given by

$$
t \tilde {\nu} (z) = \left\{ \begin{array}{l l} 0, & z \in \Omega , \\ t (\nu \circ \mathrm{g} ^ {- 1}) (z) \frac {\overline {{\mathrm{g} _ {z} ^ {- 1} (z)}}}{\mathrm{g} _ {z} ^ {- 1} (z)}, & z \in \Omega^ {*}. \end{array} \right.
$$

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

<!-- page 34 of 136 -->

2. $T(1)$ AS A HILBERT MANIFOLD

25

It follows from (1.26) that

$$
D _ {0} \left(\beta \circ R _ {[ \mu ]}\right) (\nu) \left(\mathrm{f} ^ {- 1} (z)\right) \left(\mathrm{f} _ {z} ^ {- 1} (z)\right) ^ {2} = \dot {v} _ {z z z} (z) = - \frac {6}{\pi} \iint_ {\Omega^ {*}} \frac {\tilde {\nu} (u)}{(u - z) ^ {4}} d ^ {2} u.\tag{2.1}
$$

Let $\rho_{1}(z) = (\rho \circ \mathrm{f}^{-1})(z)|\mathrm{f}_{z}^{-1}(z)|^{2}$ and $\rho_{2}(z) = (\rho \circ \mathrm{g}^{-1})(z)|\mathrm{g}_{z}^{-1}(z)|^{2}$ be the hyperbolic metric densities on the domains $\Omega$ and $\Omega^{*}$ respectively. Classical inequalities (see e.g., [Leh87, Nag88])

$$
\frac {1}{4} \leq \eta_ {i} ^ {2} (z) \rho_ {i} (z) \leq 4, \quad i = 1, 2,
$$

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

where $\eta_1(z)$ and $\eta_2(z)$ stand, respectively, for the distances of $z\in \Omega$ and $z\in \Omega^{*}$ to the quasi-circle $\mathrm{f}(S^1)$, yield the following estimates (cf. [Nag88, Sect. 3.4.5])

$$
\iint_ {\Omega} \frac {d ^ {2} z}{| u - z | ^ {4}} \leq \iint_ {| z - u | \geq \eta_ {2} (u)} \frac {d ^ {2} z}{| u - z | ^ {4}} = \frac {\pi}{\eta_ {2} (u) ^ {2}} \leq 4 \pi \rho_ {2} (u), u \in \Omega^ {*},
$$

and

$$
\iint_ {\Omega^ {*}} \frac {d ^ {2} u}{| u - z | ^ {4}} \leq 4 \pi \rho_ {1} (z), z \in \Omega .
$$

From here it follows

$$
\begin{array}{l} \| D _ {0} \left(\beta \circ R _ {[ \mu ]}\right) (\nu) \| _ {2} ^ {2} = \iint_ {\mathbb {D}} \big | D _ {0} \left(\beta \circ R _ {[ \mu ]}\right) (\nu) \big | ^ {2} \rho^ {- 1} d ^ {2} z = \iint_ {\Omega} \big | \dot {v} _ {z z z} \big | ^ {2} \rho_ {1} ^ {- 1} d ^ {2} z \\ \leq \frac {6 ^ {2}}{\pi^ {2}} \iint_ {\Omega} \rho_ {1} (z) ^ {- 1} \iint_ {\Omega^ {*}} \frac {d ^ {2} v}{| v - z | ^ {4}} \iint_ {\Omega^ {*}} \frac {| \tilde {\nu} (u) | ^ {2} d ^ {2} u}{| u - z | ^ {4}}   d ^ {2} z \\ \leq \frac {6 ^ {2} \cdot 4}{\pi} \iint_ {\Omega} \iint_ {\Omega^ {*}} \frac {| \tilde {\nu} (u) | ^ {2} d ^ {2} u}{| u - z | ^ {4}}   d ^ {2} z \leq 6 ^ {2} \cdot 4 ^ {2} \iint_ {\Omega^ {*}} | \tilde {\nu} (u) | ^ {2} \rho_ {2} (u) d ^ {2} u \\ = 6 ^ {2} \cdot 4 ^ {2} \iint_ {\mathbb {D} ^ {*}} | \nu | ^ {2} \rho (u) d ^ {2} u = 5 7 6 \| \nu \| _ {2} ^ {2}. \end{array}
$$

To prove that the mapping $D_0 \left( \beta \circ R_{[\mu]} \right)$ is onto, we adapt to our case Bers' arguments, as presented in [Nag88, Sect. 3.5]. For $\phi \in A_2(\mathbb{D})$ set $q = (\phi \circ \mathrm{f}^{-1})(\mathrm{f}_z^{-1})^2$, and choose $\mu$ in the equivalence class of $[\mu] \in T(1)$ to be the conformally natural extension of $(\mathrm{g}^{-1} \circ \mathrm{f})|_{S^1}$, constructed by Douady and Earle [DE86]. Let $h$ be the corresponding quasiconformal reflection [EN88] on $\mathbb{C}$ which fixes the quasi-circle $\mathrm{f}(S^1)$. According to the Bers reproducing formula [Ber66],

$$
q (z) = - \frac {3}{\pi} \iint_ {\Omega^ {*}} \frac {q (h (u)) (u - h (u)) ^ {2} h _ {\bar {u}} (u)}{(u - z) ^ {4}} d ^ {2} u.\tag{2.2}
$$

Analogous to $L^{\infty}(\mathbb{D}^{*})$ and $\Omega^{-1,1}(\mathbb{D}^{*})$, consider the Banach spaces $L^{\infty}(\Omega^{*})$ and

$$
\Omega^ {- 1, 1} (\Omega^ {*}) = \{\mu \in L ^ {\infty} (\Omega^ {*}): \mu = \rho_ {2} ^ {- 1} \bar {q}, q
$$

$$
\left. \Omega^ {*} \right\}
$$

Denote by $\tilde{P}$ the corresponding projection $\tilde{P}:L^{\infty}(\Omega^{*})\to \Omega^{-1,1}(\Omega^{*})$. The mapping

$$
\mu \mapsto (\mathrm{g} ^ {*}) ^ {- 1} (\mu) = \mu \circ \mathrm{g} ^ {- 1} \frac {\overline {{(\mathrm{g} ^ {- 1}) ^ {\prime}}}}{(\mathrm{g} ^ {- 1}) ^ {\prime}}
$$

<!-- page 35 of 136 -->

26

1. CURVATURE PROPERTIES AND CHERN FORMS

establishes the isomorphisms $L^{\infty}(\mathbb{D}^{*})\simeq L^{\infty}(\Omega^{*})$ and $\Omega^{-1,1}(\mathbb{D}^{*})\simeq \Omega^{-1,1}(\Omega^{*})$, and $\tilde{P} = (\mathrm{g}^{*})^{-1}\circ P\circ \mathrm{g}^{*}$. Define $\nu \in \Omega^{-1,1}(\mathbb{D}^*)$ by

$$
(\mathrm{g} ^ {*}) ^ {- 1} (\nu) (z) = \tilde {P} \left(\frac {1}{2} (q (h (z)) (z - h (z)) ^ {2} h _ {\bar {z}} (z)\right) \in \Omega^ {- 1, 1} (\Omega^ {*}).
$$

The comparison between (2.2) and (2.1) shows that

$$
D _ {0} \left(\beta \circ R _ {[ \mu ]}\right) (\nu) = \phi .
$$

To prove that $\nu \in H^{-1,1}(\mathbb{D}^*)$ we use the Earle-Nag [EN88] estimate,

$$
\frac {1}{C} \leq | z - h (z) | ^ {4} \rho_ {1} (h (z)) \rho_ {2} (z) \leq C, z \in \Omega^ {*},\tag{2.3}
$$

where the constant $C$ depends only on $\| \mu \|_{\infty}$. Since the operator $\tilde{P}$ gives the orthogonal projection of $L^2 (\Omega^*,\rho_2(z)d^2 z)$ onto $H^{-1,1}(\Omega^{*})$, we get by the Earle-Nag inequality

$$
\begin{array}{l} \iint_ {\mathbb {D} ^ {*}} | \nu | ^ {2} \rho (z) d ^ {2} z = \iint_ {\Omega^ {*}} | (g ^ {*}) ^ {- 1} (\nu) (z) | ^ {2} \rho_ {2} (z) d ^ {2} z \\ \qquad \qquad \leq \frac {1}{4} \iint_ {\Omega^ {*}} | q (h (z)) (z - h (z)) ^ {2} h _ {\bar {z}} (z) | ^ {2} \rho_ {2} (z) d ^ {2} z \\ \qquad \qquad \leq \frac {C}{4} \iint_ {\Omega^ {*}} | q (h (z)) h _ {\bar {z}} (z) | ^ {2} \rho_ {1} ^ {- 1} (h (z)) d ^ {2} z. \end{array}
$$

Since $h$ is sense reversing, for

$$
\kappa = \frac{h_{z}^{-1}}{h_{\bar{z}}^{-1}}
$$

we have $\| \kappa \|_{\infty} < 1$. Now

$$
\left| \begin{array}{l} \iint_ {\Omega^ {*}} | q (h (z)) h _ {\bar {z}} (z) | ^ {2} \rho_ {1} (h (z)) ^ {- 1} d ^ {2} z \\ = \iint_ {\Omega} | q (z) | ^ {2} \rho_ {1} (z) ^ {- 1} | (h _ {\bar {z}} \circ h ^ {- 1}) (z) h _ {\bar {z}} ^ {- 1} (z) | ^ {2} (1 - | \kappa (z) | ^ {2}) d ^ {2} z \\ = \iint_ {\Omega} \frac {| q (z) | ^ {2}}{1 - | \kappa (z) | ^ {2}} \rho_ {1} (z) ^ {- 1} d ^ {2} z \\ \leq C _ {1} \iint_ {\Omega} | q (z) | ^ {2} \rho_ {1} (z) ^ {- 1} d ^ {2} z = C _ {1} \| \phi \| _ {2} ^ {2} <   \infty , \end{array} \right|
$$

so that $\| \nu \| _2\leq C_2\| \phi \| _2$. This also proves that the inverse map to $D_0\left(\beta \circ R_{[\mu ]}\right)$ is bounded, so that $D_0\left(\beta \circ R_{[\mu ]}\right)$ is a topological isomorphism.

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

REMARK 2.4. It follows from the proof of the first part of Theorem 2.3 that the operator $D_0(\beta \circ R_{[\mu]}) = D_0(\beta \circ \Phi \circ R_\mu)$ extends to the bounded linear operator on $L^2 (\mathbb{D}^*,\rho (z)d^2 z)$ and the estimate

$$
\| D _ {0} (\beta \circ \Phi \circ R _ {\mu}) (\nu) \| _ {2} = \| D _ {\mu} (\beta \circ \Phi) (D _ {0} R _ {\mu} (\nu)) \| _ {2} \leq 2 4 \| \nu \| _ {2}
$$

holds for all $\nu \in L^{2}(\mathbb{D}^{*},\rho (z)d^{2}z)$ and $\mu \in L^{\infty}(\mathbb{D}^{*})_{1}$.

<!-- page 36 of 136 -->

2. $T(1)$ AS A HILBERT MANIFOLD

27

2.2. The $L^2$-estimates. The lemmas below are needed for the rigorous definition of a complex Hilbert manifold structure on $T(1)$.

LEMMA 2.5. For every $\varepsilon > 0$ there exists $0 < \delta < 1$ such that for all $\mu \in \Omega^{-1,1}(\mathbb{D}^*)$ with $\| \mu \|_{\infty} < \delta$,

$$
\left| \frac {| (w _ {\mu}) _ {z} (z) | ^ {2}}{(1 - | w _ {\mu} (z) | ^ {2}) ^ {2}} - \frac {1}{(1 - | z | ^ {2}) ^ {2}} \right| <   \frac {\varepsilon}{(1 - | z | ^ {2}) ^ {2}}
$$

for all $z \in \mathbb{D} \cup \mathbb{D}^*$. The same inequality holds for $w_{\mu^{-1}} = w_{\mu}^{-1}$.

PROOF. Using the isomorphism $\Omega^{-1,1}(\mathbb{D}^*) \xrightarrow{\sim} \Omega^{-1,1}(\mathbb{D})$ given by reflection (1.1) and property (1.2), it is sufficient to prove the estimate for $z \in \mathbb{D}$. Since $\mathrm{g}_{\mu} = \alpha \circ w_{\mu}$, where $\alpha \in \mathrm{PSU}(1,1)$, the estimate holds for $w_{\mu}$ if and only if it holds for $\mathrm{g}_{\mu}$. By Lemma 1.5 $\mathrm{g}_{\mu}$ fixes 0 and $\infty$, and by the result of Ahlfors and Bers in [AB60] (see also the remark of Bers in [Ber73]) the functional

$$
\mathcal {L} ^ {\infty} (\mathbb {D} ^ {*}) _ {1} \ni \mu \mapsto (g _ {\mu}) _ {z} (0) \in \mathbb {C}
$$

is real-analytic at $\mu = 0$. In particular, for every $\varepsilon > 0$ there exists $0 < \delta < 1$ such that for all $\mu \in \Omega^{-1,1}(\mathbb{D}^*)_1$ with $\| \mu \|_{\infty} < \delta$,

$$
\left| | (\mathrm{g} _ {\mu}) _ {z} (0) | ^ {2} - 1 \right| <   \varepsilon .
$$

For $z \in \mathbb{D}$, let $\tilde{\mu} = \mu \circ \sigma_z$, where $\sigma_z(w) = \frac{w + z}{1 + \bar{z}w}$. Then $g_{\tilde{\mu}} = \tilde{\sigma}_z \circ g_{\mu} \circ \sigma_z$ for some $\tilde{\sigma}_z \in \mathrm{PSU}(1,1)$. Since $\tilde{\mu} \in \Omega^{-1,1}(\mathbb{D}^*)_1$, it follows from Lemma 1.5 that $g_{\tilde{\mu}}(0) = 0$. Therefore from $\tilde{\sigma}_z(g_{\mu}(z)) = 0$, one obtains

$$
\frac {| (\mathrm{g} _ {\mu}) _ {z} (z) | ^ {2}}{(1 - | \mathrm{g} _ {\mu} (z) | ^ {2}) ^ {2}} (1 - | z | ^ {2}) ^ {2} = | (\mathrm{g} _ {\bar {\mu}}) _ {z} (0) | ^ {2}.
$$

Since $\| \tilde{\mu} \|_{\infty} = \| \mu \|_{\infty}$, the assertion follows. On the other hand, if $\mu \in \Omega^{-1,1}(\mathbb{D}^{*})_{1}$, then $\mu^{-1} \in \mathcal{L}^{\infty}(\mathbb{D}^{*})_{1}$ and $\| \mu^{-1} \|_{\infty} = \| \mu \|_{\infty}$. Hence the assertion also holds for $w_{\mu^{-1}}$.

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

COROLLARY 2.6. Let $\mu \in \Omega^{-1,1}(\mathbb{D}^*)$, $\| \mu \|_{\infty} < \delta$, where $\delta$ corresponds to $\varepsilon = 1$ in the previous lemma. Then for every $\lambda \in L^{\infty}(\mathbb{D}^{*})_{1}$ the linear mapping $D_{\lambda}R_{\mu}$ extends to an invertible bounded linear operator on the Hilbert space $L^2 (\mathbb{D}^*,\rho (z)d^2 z)$. Moreover,

$$
\boxed {\left\| D _ {\lambda} R _ {\mu} (\nu) \right\| _ {2} \leq \frac {\sqrt {2}}{(1 - \| \mu \| _ {\infty}) ^ {2}} \| \nu \| _ {2},}
$$

for all $\nu \in L^{2}(\mathbb{D}^{*},\rho (z)d^{2}z)$ and $\lambda \in L^{\infty}(\mathbb{D}^{*})_{1}$. The same inequality holds for $D_{\lambda}R_{\mu^{-1}}$.

PROOF. Since

$$
D _ {\lambda} R _ {\mu} (\nu) = \frac {(1 - | \mu | ^ {2}) \nu \circ w _ {\mu}}{\left(1 + \overline {{\mu}} \lambda \circ w _ {\mu} \frac {\overline {{(w _ {\mu}) _ {z}}}}{(w _ {\mu}) _ {z}}\right) ^ {2}} \frac {\overline {{(w _ {\mu}) _ {z}}}}{(w _ {\mu}) _ {z}},
$$

and

$$
\left\| \frac {1 - | \mu | ^ {2}}{\left(1 + \overline {{\mu}} \lambda \circ w _ {\mu} \frac {\overline {{(w _ {\mu}) _ {z}}}}{(w _ {\mu}) _ {z}}\right) ^ {2}} \right\| _ {\infty} \leq \frac {1}{(1 - \| \mu \| _ {\infty}) ^ {2}}
$$

<!-- page 37 of 136 -->

28

1. CURVATURE PROPERTIES AND CHERN FORMS

for all $\lambda \in L^{\infty}(\mathbb{D}^{*})_{1}$, we have by using Lemma 2.5 and $\| \mu \|_{\infty} = \| \mu^{-1} \|_{\infty}$,

$$
\begin{array}{l} \iint_ {\mathbb {D} ^ {*}} \Big | D _ {\lambda} R _ {\mu} (\nu) \Big | ^ {2} \rho (z) d ^ {2} z \leq (1 - \| \mu \| _ {\infty}) ^ {- 4} \iint_ {\mathbb {D} ^ {*}} \bigg | \nu \circ w _ {\mu} \frac {\overline {{(w _ {\mu}) _ {z}}}}{(w _ {\mu}) _ {z}} \bigg | ^ {2} \rho (z) d ^ {2} z \\ = (1 - \| \mu \| _ {\infty}) ^ {- 4} \iint_ {\mathbb {D} ^ {*}} | \nu | ^ {2} \frac {4 | (w _ {\mu^ {- 1}}) _ {z} | ^ {2}}{(1 - | w _ {\mu^ {- 1}} | ^ {2}) ^ {2}} (1 - | \mu^ {- 1} | ^ {2}) d ^ {2} z \\ \leq 2 (1 - \| \mu \| _ {\infty}) ^ {- 4} \iint_ {\mathbb {D} ^ {*}} | \nu | ^ {2} \rho (z) d ^ {2} z = 2 (1 - \| \mu | _ {\infty}) ^ {- 4} \| \nu \| _ {2} ^ {2}. \end{array}
$$

Replacing everywhere $\mu$ by $\mu^{-1}$ we get the same estimate for $D_{\lambda}R_{\mu^{-1}}$.

Denote by $\mathcal{O}(\mathbb{D}^{*})_{1}$ the subgroup of $L^{\infty}(\mathbb{D}^{*})_{1}$ generated by $\mu \in \Omega^{-1,1}(\mathbb{D}^{*})$, $\| \mu \|_{\infty} < \delta$, where $\delta$ is as in Corollary 2.6.

LEMMA 2.7. For every $\mu \in \mathcal{O}(\mathbb{D}^*)_1$ there exists $C > 0$ such that

$$
\| R _ {\mu} (\lambda_ {1}) - R _ {\mu} (\lambda_ {2}) \| _ {2} <   C \| \lambda_ {1} - \lambda_ {2} \| _ {2}
$$

for all $\lambda_1, \lambda_2 \in L^\infty(\mathbb{D}^*)_1$ satisfying $\lambda_1 - \lambda_2 \in L^2(\mathbb{D}^*, \rho(z)d^2z)$.

PROOF. Suppose first that $\| \mu \|_{\infty} < \delta$. Set $\lambda(t) = \lambda_1 + t\nu$, where $\nu = \lambda_2 - \lambda_1$, so that $\lambda(t) \in L^{\infty}(\mathbb{D}^{*})_{1}$, $0 \leq t \leq 1$. By fundamental theorem of calculus,

$$
\begin{array}{c} R _ {\mu} (\lambda_ {1}) - R _ {\mu} (\lambda_ {2}) = \int_ {0} ^ {1} \frac {d}{d t} R _ {\mu} (\lambda (t)) d t \\ = \int_ {0} ^ {1} D _ {\lambda (t)} R _ {\mu} (\nu) d t. \end{array}
$$

Using Corollary 2.6,

$$
\begin{array}{l} \| R _ {\mu} (\lambda_ {1}) - R _ {\mu} (\lambda_ {2}) \| _ {2} ^ {2} = \iint_ {\mathbb {D} ^ {*}} \left| \int_ {0} ^ {1} D _ {\lambda (t)} R _ {\mu} (\nu) (z) \right| ^ {2} \rho (z) d ^ {2} z \\ \qquad \leq \int_ {0} ^ {1} \left(\iint_ {\mathbb {D} ^ {*}} \left| D _ {\lambda (t)} R _ {\mu} (\nu) (z) \right| ^ {2} \rho (z) d ^ {2} z\right) d t \\ \qquad \leq C ^ {2} \| \nu \| _ {2} ^ {2} = C ^ {2} \| \lambda_ {1} - \lambda_ {2} \| _ {2} ^ {2}. \end{array}
$$

The same estimate also holds for $R_{\mu}^{-1}$.

Since every $\mu \in \mathcal{O}(\mathbb{D}^{*})_{1}$ can be written as $\mu_n^{\varepsilon_n}*\dots *\mu_1^{\varepsilon_1}$, where $\mu_i\in \Omega^{-1,1}(\mathbb{D}^*)$, $\| \mu_i\|_{\infty} < \delta$, and $\varepsilon_{i} = \pm 1$, $i = 1,\dots ,n$, we have

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

$$
R _ {\mu} = R _ {\mu_ {1}} ^ {\varepsilon_ {1}} \circ \dots \circ R _ {\mu_ {n}} ^ {\varepsilon_ {n}},
$$

and the assertion of the lemma follows.

REMARK 2.8. Applying the same argument, we get from Corollary 2.6 that for every $\mu \in \mathcal{O}(\mathbb{D}^{*})_{1}$ there exists $C > 0$, depending only on $\| \mu \|_{\infty}$ such that

$$
\left\| D _ {\lambda} R _ {\mu} (\nu) \right\| _ {2} \leq C \| \nu \| _ {2},
$$

for all $\nu \in L^{2}(\mathbb{D}^{*},\rho (z)d^{2}z)$ and $\lambda \in L^{\infty}(\mathbb{D}^{*})_{1}$.

<!-- page 38 of 136 -->

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

2. $T(1)$ AS A HILBERT MANIFOLD

29

LEMMA 2.9. For every $\mu \in \mathcal{O}(\mathbb{D}^{*})_{1}$ there exists $C > 0$ such that


> **[ERRATUM W2-10]** (1724–1730 (used 1886, 1946, 1984, 2060–2082, 4056); Lean: `lemma_2_9` (S2:2004; Round-3 D3)) uniform `C` (independent of `‖λ‖∞`) suspected false (`λ_k = kχ_B`, `k → 1`: `‖λ_k‖₂` bounded, `[λ_k] → ∞`); the proof applies Remark 2.8 to non-`𝒪` elements (and TT:1946 applies the lemma with `μ = λ⁻¹`). The restricted form suffices for Thm 2.10/2.13.

$$
\| (\beta \circ \Phi) (\lambda * \mu) - (\beta \circ \Phi) (\mu) \| _ {2} \leq C \| \lambda \| _ {2}
$$

for all $\lambda \in L^{2}(\mathbb{D}^{*},\rho (z)d^{2}z)\cap L^{\infty}(\mathbb{D}^{*})_{1}$.

PROOF. Set $\phi(t) = (\beta \circ \Phi)(t\lambda * \mu)$. By fundamental theorem of calculus,

$$
(\beta \circ \Phi) (\lambda * \mu) - (\beta \circ \Phi) (\mu) = \int_ {0} ^ {1} \frac {d \phi}{d t} (t) d t,
$$

where

$$
\frac {d \phi}{d t} (t) = D _ {t \lambda} \left(\beta \circ \Phi \circ R _ {\mu}\right) (\lambda) = \left(D _ {t \lambda * \mu} \left(\beta \circ \Phi\right) \circ D _ {t \lambda} R _ {\mu}\right) (\lambda)
$$

by chain rule. Since $(D_0R_\mu)^{-1} = D_\mu R_\mu^{-1}$, it follows from Remarks 2.4 and 2.8 that

$$
\| D _ {t \lambda * \mu} (\beta \circ \Phi) (\nu) \| _ {2} \leq 2 4 \| D _ {t \lambda * \mu} R _ {(t \lambda * \mu) ^ {- 1}} (\nu) \| _ {2} \leq C _ {1} \| \nu \| _ {2}.
$$

Using Remark 2.8 again, we get

$$
\left\| \frac {d \phi}{d t} (t) \right\| _ {2} = \left\| \left(D _ {t \lambda * \mu} (\beta \circ \Phi) \circ D _ {t \lambda} R _ {\mu}\right) (\lambda) \right\| _ {2} \leq C _ {2} \| \lambda \| _ {2}, 0 \leq t \leq 1.
$$

Therefore,

$$
\begin{array}{l} \big \| (\beta \circ \Phi) (\lambda * \mu) - (\beta \circ \Phi) (\mu) \big \| _ {2} ^ {2} = \iint_ {\mathbb {D}} \left| \int_ {0} ^ {1} \frac {d \phi}{d t} (t, z) d t \right| ^ {2} \rho (z) ^ {- 1} d ^ {2} z \\ \qquad \qquad \qquad \leq \int_ {0} ^ {1} \left(\iint_ {\mathbb {D}} \big | \frac {d \phi}{d t} (t, z) \big | ^ {2} \rho (z) ^ {- 1} d ^ {2} z\right) d t \\ \qquad \qquad \qquad \leq C _ {2} ^ {2} \big \| \lambda \big \| _ {2} ^ {2}, \end{array}
$$

which concludes the proof.

2.3. The Hilbert manifold structure of $T(1)$. For every $\mu \in \mathcal{O}(\mathbb{D}^*)_1$ let $V_{\mu} \subset U_{\mu} \subset T(1)$ be the image under the map $h_{\mu}^{-1} = \Phi \circ R_{\mu} \circ \Lambda$ of the open ball of radius $\sqrt{\pi/3}$ about the origin in $A_2(\mathbb{D})$, which by Lemma 2.1 is contained in the ball of radius 2 in $A_{\infty}(\mathbb{D})$. Here $(U_{\mu}, h_{\mu})$ is the coordinate chart $U_{\mu}$ of the complex-analytic atlas for $T(1)$ as a complex Banach manifold (see Section 1.1.4). Let

$$
\tilde {h} _ {\mu} = h _ {\mu} \big | _ {V _ {\mu}}: V _ {\mu} \to A _ {2} (\mathbb {D}).
$$

The main result of this subsection is the following.

THEOREM 2.10. For every $\mu, \nu \in \mathcal{O}(\mathbb{D}^*)_1$ the sets $\tilde{h}_{\mu}(V_{\mu} \cap V_{\nu})$ and $\tilde{h}_{\nu}(V_{\mu} \cap V_{\nu})$ are open in $A_2(\mathbb{D})$ and the map

$$
\tilde {h} _ {\mu \nu} = \tilde {h} _ {\mu} \circ \tilde {h} _ {\nu} ^ {- 1}: \tilde {h} _ {\nu} (V _ {\mu} \cap V _ {\nu}) \longrightarrow \tilde {h} _ {\mu} (V _ {\mu} \cap V _ {\nu}) \subset A _ {2} (\mathbb {D})
$$

is a biholomorphic function on the Hilbert space $A_{2}(\mathbb{D})$.

PROOF. First we prove that the sets $\tilde{h}_{\mu}(V_{\mu} \cap V_{\nu})$ and $\tilde{h}_{\nu}(V_{\mu} \cap V_{\nu})$ are open in $A_2(\mathbb{D})$. Since $V_{\mu} \cap V_{\nu} \neq \emptyset$ (otherwise there is nothing to prove), there exist $\phi_1 \in \tilde{h}_{\mu}(V_{\mu} \cap V_{\nu})$ and $\phi_2 \in \tilde{h}_{\nu}(V_{\mu} \cap V_{\nu})$, $\| \phi_1 \|_2, \| \phi_2 \|_2 < \sqrt{\pi / 3}$, such that $\tilde{h}_{\mu}^{-1}(\phi_1) = \tilde{h}_{\nu}^{-1}(\phi_2)$, i.e.,

$$
(\Phi \circ R _ {\mu} \circ \Lambda) (\phi_ {1}) = (\Phi \circ R _ {\nu} \circ \Lambda) (\phi_ {2}).
$$

<!-- page 39 of 136 -->

30

1. CURVATURE PROPERTIES AND CHERN FORMS

Setting $\lambda_{1} = \Lambda (\phi_{1}),\lambda_{2} = \Lambda (\phi_{2})$ and $\kappa = \nu *\mu^{-1}$, we get

$$
\Phi (\lambda_ {1}) = \Phi (\lambda_ {2} * \kappa).
$$

The sets $h_{\mu}(U_{\mu} \cap U_{\nu})$ and $h_{\nu}(U_{\mu} \cap U_{\nu})$ are open in $A_{\infty}(\mathbb{D})$, so that there exists $\delta_1 > 0$ such that $h_{\mu}(U_{\mu} \cap U_{\nu})$ contains a ball of radius $\delta_1$ about $\phi_1$ in $A_{\infty}(\mathbb{D})$. The mapping $h_{\mu\nu}: h_{\nu}(U_{\mu} \cap U_{\nu}) \to h_{\mu}(U_{\mu} \cap U_{\nu}) \subset A_{\infty}(\mathbb{D})$ is a continuous function in the Banach space $A_{\infty}(\mathbb{D})$, so that there exists $\delta_2 > 0$ such that the inverse image by $h_{\mu\nu}$ of the ball of radius $\delta_1$ about $\phi_1$ in $A_{\infty}(\mathbb{D})$ contains the ball of radius $\delta_2$ about $\phi_2$ in $A_{\infty}(\mathbb{D})$. According to Lemma 2.1, the latter ball contains any ball of radius $\delta_3 < \sqrt{\pi/12} \delta_2$ about $\phi_2$ in $A_2(\mathbb{D})$. Now for every $\varphi_2 \in A_2(\mathbb{D})$ satisfying $\| \varphi_2 - \phi_2 \|_2 < \delta_3$ set

$$
\varphi_ {1} = h _ {\mu \nu} (\varphi_ {2}) = (\beta \circ \Phi \circ R _ {\kappa} \circ \Lambda) (\varphi_ {2}).
$$

We claim that $\delta_3 > 0$ can be chosen such that $\varphi_1 \in A_2(\mathbb{D})$ and $\| \varphi_1 \|_2 < \sqrt{\pi / 3}$, which implies that $\tilde{h}_{\nu}(V_{\mu} \cap V_{\nu})$ contains the ball of radius $\delta_3$ about $\phi_2$ in $A_2(\mathbb{D})$. Indeed, set $\lambda = \Lambda(\varphi_2)$, so that $\varphi_1 = (\beta \circ \Phi)(\lambda * \kappa)$. Since $\lambda - \lambda_2 \in L^2(\mathbb{D}^*, \rho(z)d^2z)$, we have by Lemmas 2.9 and 2.7,

$$
\begin{array}{r l} & {\| \varphi_ {1} - \phi_ {1} \| _ {2} = \| (\beta \circ \Phi) (\lambda * \kappa) - (\beta \circ \Phi) (\lambda_ {2} * \kappa) \| _ {2}} \\ & {\qquad \leq C \| \lambda * \lambda_ {2} ^ {- 1} \| _ {2} \leq C ^ {2} \| \lambda - \lambda_ {2} \| _ {2}} \\ & {\qquad = 2 C ^ {2} \| \varphi_ {2} - \phi_ {2} \| _ {2} <   2 C ^ {2} \delta_ {3},} \end{array}
$$

where the constant $C > 0$ (chosen to be the same for both Lemmas 2.7 and 2.9) depends only on $\lambda_{2}$ and $\kappa$. Choosing $\delta_3$ small enough we have $\| \varphi_1\| _2 < \sqrt{\pi / 3}$.

The same argument applied to the map $\tilde{h}_{\nu \mu} = \tilde{h}_{\mu \nu}^{-1}$ proves that $\tilde{h}_{\mu}(V_{\mu}\cap V_{\nu})$ is open in $A_{2}(\mathbb{D})$.

It remains to prove that the map $\tilde{h}_{\mu\nu}$ is a holomorphic function in the Hilbert space $A_2(\mathbb{D})$. It is bounded, so according to [Bou67] it is sufficient to prove that for every $\varphi \in \tilde{h}_{\nu}(V_{\mu} \cap V_{\nu})$ and every $\eta \in A_2(\mathbb{D})$ the mapping $\mathbb{C} \ni t \mapsto \phi(t) = \tilde{h}_{\mu\nu}(\varphi + t\eta) \in A_2(\mathbb{D})$ is a holomorphic function in some neighborhood of 0 in $\mathbb{C}$. For this purpose we use the standard argument based on the fact that the map $h_{\mu\nu}$ is already a holomorphic function in the Banach space $A_{\infty}(\mathbb{D})$ and the mapping $\mathbb{C} \ni t \mapsto \phi(t) \in A_{\infty}(\mathbb{D})$ is a holomorphic function in some neighborhood of 0 in $\mathbb{C}$. Thus there exists $\delta > 0$ such that for every $|t_0| < \delta$,

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

$$
\left\| \phi (t) - \phi (t _ {0}) - (t - t _ {0}) \frac {d \phi}{d t} (t _ {0}) \right\| _ {\infty} = o (| t - t _ {0} |) \quad \text {as} \quad t \to t _ {0}.
$$

Moreover, $\delta$ can be chosen such that $\varphi + t\eta \in \tilde{h}_{\nu}(V_{\mu} \cap V_{\nu})$ for $|t| < \delta$. Then for every $z \in \mathbb{D}$ the complex-valued function $\phi(t)(z)$ is holomorphic on $|t| < \delta$ and

$$
\begin{array}{c} \phi (t, z) - \phi (t _ {0}, z) - (t - t _ {0}) \frac {d \phi}{d t} (t _ {0}, z) \\ = \frac {1}{2 \pi i} \oint_ {| w - t _ {0} | = \delta_ {1}} \phi (w, z) \left(\frac {1}{w - t} - \frac {1}{w - t _ {0}} - \frac {t - t _ {0}}{(w - t _ {0}) ^ {2}}\right) d w \\ = \frac {(t - t _ {0}) ^ {2}}{2 \pi i} \oint_ {| w - t _ {0} | = \delta_ {1}} \frac {\phi (w , z)}{(w - t _ {0}) ^ {2} (w - t)} d w, \end{array}
$$

where $\delta_1 > 0$ is such that the disk of radius $\delta_1$ about $t_0$ is inside the disk of radius $\delta$ about the origin, and $t$ satisfies $|t - t_0| < \delta_1$. Since $\phi(t) \in \tilde{h}_{\mu}(V_{\mu} \cap V_{\nu})$, $\|\phi(t)\|_2^2 < \pi/3$

<!-- page 40 of 136 -->

2. $T(1)$ AS A HILBERT MANIFOLD

31

for all $|t| < \delta$, and we have

$$
\begin{array}{r l} & {\left\| \frac {\phi (t) - \phi (t _ {0})}{t - t _ {0}} - \frac {d \phi}{d t} (t _ {0}) \right\| _ {2} ^ {2}} \\ & {\leq \frac {| t - t _ {0} | ^ {2}}{4 \pi^ {2}} \oint_ {| w | = \delta_ {1}} \frac {| d w |}{| w | ^ {4} | w - (t - t _ {0}) | ^ {2}} \oint_ {| w | = \delta_ {1}} \left\| \phi (w + t _ {0}) \right\| _ {2} ^ {2} | d w |} \\ & {= O (| t - t _ {0} | ^ {2}) \quad \mathrm{as} \quad t \to t _ {0}.} \end{array}
$$

According to [Bou67], Theorem 2.10 justifies the following definition.

DEFINITION 2.11. The covering

$$
T (1) = \bigcup_ {\mu \in \mathcal {O} (\mathbb {D} ^ {*}) _ {1}} V _ {\mu}
$$

with the coordinate maps $\tilde{h}_{\mu}:V_{\mu}\longrightarrow A_{2}(\mathbb{D})$ and the transition maps

$$
\tilde {h} _ {\mu \nu} = \tilde {h} _ {\mu} \circ \tilde {h} _ {\nu} ^ {- 1}: \tilde {h} _ {\nu} (V _ {\mu} \cap V _ {\nu}) \longrightarrow \tilde {h} _ {\mu} (V _ {\mu} \cap V _ {\nu})
$$

is a complex-analytic atlas which endows $T(1)$ with the structure of a complex Hilbert manifold modeled on the Hilbert space $A_2(\mathbb{D})$.

COROLLARY 2.12. The right translations are biholomorphic mappings on the Hilbert manifold $T(1)$.

PROOF. Representing a point in $T(1)$ by $\mu \in \mathcal{O}(\mathbb{D}^{*})_{1}$ we have $R_{[\mu]}(V_{\lambda}) = V_{\lambda * \mu}$, so that $\tilde{h}_{\lambda * \mu} \circ R_{[\mu]} \circ \tilde{h}_{\lambda}^{-1}$ is the identity mapping on $\tilde{h}_{\lambda}(V_{\lambda}) \subset A_2(\mathbb{D})$.

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026for download from IP 130.34.46.51.

We will continue to use the name Bers coordinates for the complex coordinates $(V_{\mu},\tilde{h}_{\mu})$ on the Hilbert manifold $T(1)$. As in Section 1.1.4, the vector field $\frac{\partial}{\partial\varepsilon_{\nu}}$ corresponding to $\nu \in H^{-1,1}(\mathbb{D}^*)$ at a point $[\mu] \in V_0$ in terms of the Bers coordinates on $V_{\mu}$ has the same form (1.5), i.e.,

$$
\left. \frac {\partial}{\partial \varepsilon_ {\nu}} \right| _ {[ \mu ]} = P \left(\left(\frac {\nu}{1 - | \mu | ^ {2}} \frac {(w _ {\mu}) _ {z}}{(\overline {{w}} _ {\mu}) _ {\bar {z}}}\right) \circ w _ {\mu} ^ {- 1}\right),
$$

where $P:L^{2}(\mathbb{D}^{*},\rho (z)d^{2}z)\to H^{-1,1}(\mathbb{D}^{*})$ is the orthogonal projector given by (1.7).

2.4. Integral manifolds of the distribution $\mathfrak{D}_T$. Finally, we introduce a Hilbert manifold structure on the Banach space $A_{\infty}(\mathbb{D})$ by defining the coordinate chart at every $\phi \in A_{\infty}(\mathbb{D})$ to be $\phi + A_2(\mathbb{D})$. By Lemma 2.1 the Hilbert manifold topology on $A_{\infty}(\mathbb{D})$ is stronger than the Banach space topology. The Hilbert manifold $A_{\infty}(\mathbb{D})$ is not connected. Rather $A_{\infty}(\mathbb{D})$ is the union of uncountably many components $\phi + A_2(\mathbb{D})$ with $\phi \in A_{\infty}(\mathbb{D}) / A_2(\mathbb{D})$, which are integral manifolds of the distribution $\mathfrak{D}_A$.

THEOREM 2.13. The Bers embedding $\beta : T(1) \to \beta(T(1)) \subset A_{\infty}(\mathbb{D})$ is a bi-holomorphic mapping of Hilbert manifolds.

PROOF. To prove that the Bers embedding is holomorphic it is sufficient to show that for every $\mu \in \mathcal{O}(\mathbb{D}^*)_1$ the image of the ball of radius $\sqrt{\pi / 3}$ about 0 in

<!-- page 41 of 136 -->

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026for download from IP 130.34.46.51.

32

1. CURVATURE PROPERTIES AND CHERN FORMS

$A_{2}(\mathbb{D})$ by the mapping $\beta \circ \tilde{h}_{\mu}^{-1} = \beta \circ \Phi \circ R_{\mu} \circ \Lambda$ is inside a translate by $(\beta \circ \Phi)(\mu)$ of some ball about 0 in $A_{2}(\mathbb{D})$. This immediately follows from Lemma 2.9,

$$
\begin{array}{c} \left\| \left(\beta \circ \tilde {h} _ {\mu} ^ {- 1}\right) (\varphi) - (\beta \circ \Phi) (\mu) \right\| _ {2} = \| (\beta \circ \Phi) (\lambda * \mu) - (\beta \circ \Phi) (\mu) \| _ {2} \\ <   C \| \lambda \| _ {2}, \end{array}
$$

where $\lambda = \Lambda (\varphi)\in L^{2}(\mathbb{D}^{*},\rho (z)d^{2}z)\cap L^{\infty}(\mathbb{D}^{*})_{1}$ and the constant $C > 0$ depends only on $\| \mu \|_{\infty}$. Since the Bers embedding is a holomorphic mapping of Banach manifolds, the standard argument used in the proof of Theorem 2.10 works for this case, so that the mapping $\beta \circ \tilde{h}_{\mu}^{-1} - (\beta \circ \Phi)(\mu)$ is a holomorphic function on the Hilbert space $A_{2}(\mathbb{D})$.

Finally, the image $\beta(T(1))$ is open in the Hilbert manifold $A_{\infty}(\mathbb{D})$ since it is open in a weaker Banach manifold topology. Using Theorem 2.3 and the inverse function theorem for Hilbert manifolds [Lan95] we see that the Bers embedding is biholomorphic.

Theorem 2.13 allows us to conclude that the distribution $\mathfrak{D}_T$ on $T(1)$ is equivalent to the restriction of the distribution $\mathfrak{D}_A$ on $\beta(T(1)) \subset A_{\infty}(\mathbb{D})$, and therefore is integrable. Its integral manifolds are inverse images by the Bers embedding $\beta$ of the integral manifolds of the distribution $\mathfrak{D}_A$ on $\beta(T(1))$, i.e., of the components $(\phi + A_2(\mathbb{D})) \cap \beta(T(1))$. For every $[\mu] \in T(1)$ denote by $T_{[\mu]}(1)$ the component of the Hilbert manifold $T(1)$ containing $[\mu]$. It follows from Theorems 2.3 and 2.13 that the Hilbert manifold $T_{[\mu]}(1)$ is the integral manifold of the distribution $\mathfrak{D}_T$ passing through $[\mu] \in T(1)$. The right translations act transitively on the set of components, i.e. $R_{[\nu]}(T_{[\mu]}(1)) = T_{[\mu*\nu]}(1)$ for all $[\mu], [\nu] \in T(1)$.


> **[ERRATUM W2-11]** (1896; Lean: `componentT_spec` conj 1 (S2:2161)) for `[μ] ∉ T₀(1)` the memoir's right-translation argument needs Lemma 2.9 in the unrestricted form (W2-10); not shown false.

The component of $0 \in T(1)$ by $T_0(1)$ is denoted by $T_0(1)$.

## 3. $T_0(1)$ as a topological group

Here we prove that the connected component $T_0(1)$ of $0 \in T(1)$ in the Hilbert manifold topology is the inverse image of $\beta(T(1)) \cap A_2(\mathbb{D})$ under the Bers embedding, and that $T_0(1)$ and $\mathcal{T}_0(1) = \pi^{-1}(T_0(1))$ are topological groups.

It follows from Theorem 2.13 that to prove $T_0(1) = \beta^{-1}(\beta(T(1)) \cap A_2(\mathbb{D}))$, it is sufficient to show that $\beta(T(1)) \cap A_2(\mathbb{D})$ is connected.

THEOREM 3.1. The submanifold $\beta(T(1)) \cap A_2(\mathbb{D})$ of $\beta(T(1))$ is connected in the Hilbert manifold topology of $\beta(T(1))$.

PROOF. First, in the Hilbert manifold topology the set $\beta(\mathrm{M}\ddot{\mathrm{o}}\mathrm{b}(S^{1})\setminus\mathrm{Diff}_{+}(S^{1}))$ is dense in $\beta(T(1))\cap A_{2}(\mathbb{D})$. Indeed, since $\beta(T(1))\cap A_{2}(\mathbb{D})$ is open in $A_{2}(\mathbb{D})$, for every $\phi\in\beta(T(1))\cap A_{2}(\mathbb{D})$ there exists $\delta$ such that $\tilde{\phi}\in\beta(T(1))\cap A_{2}(\mathbb{D})$ for all $\tilde{\phi}$ satisfying $\|\tilde{\phi}-\phi\|_{2}<\delta$. Since $\phi(z)=\sum_{k=2}^{\infty}(k^{3}-k)a_{k}z^{k-2}\in A_{2}(\mathbb{D})$, for every $n\in\mathbb{N}$ there exists $N\in\mathbb{N}$ such that $\frac{\pi}{2}\sum_{k=N+1}^{\infty}(k^{3}-k)|a_{k}|^{2}<\frac{1}{n^{2}}$, so that for $\phi_{n}(z)=\sum_{k=2}^{N}(k^{3}-k)a_{k}z^{k-2}$ we have $\|\phi_{n}-\phi\|_{2}<\frac{1}{n}$. Thus for $\frac{1}{n}<\delta$ there exists $\gamma_{n}=g_{n}^{-1}\circ f_{n}\in\mathrm{M}\ddot{\mathrm{o}}\mathrm{b}(S^{1})\backslash\mathrm{Homeo}_{qs}(S^{1})$ such that $S(f_{n})=\phi_{n}$. Since $\phi_{n}$ is analytic on an open domain containing $\mathbb{D}\cup S^{1}$, so is the function $f_{n}$ and, consequently, $f_{n}(S^{1})$ is an analytic curve. Hence $\gamma_{n}|_{S^{1}}$ is smooth and $\phi_{n}\in\beta(\mathrm{M}\ddot{\mathrm{o}}\mathrm{b}(S^{1})\backslash\mathrm{Diff}_{+}(S^{1}))$.

Secondly, the inclusion

$$
\operatorname{Mob} (S ^ {1}) \backslash \operatorname{Diff} _ {+} (S ^ {1}) \hookrightarrow T (1)
$$

<!-- page 42 of 136 -->

3. $T_{0}(1)$ AS A TOPOLOGICAL GROUP

33

is a continuous mapping between the Frechet and Hilbert manifolds. Since the Frechet manifold  $\mathrm{M}\ddot{\mathrm{o}}\mathrm{b}(S^{1})\backslash\mathrm{Diff}_{+}(S^{1})$  is connected, its image in the Hilbert manifold  $T(1)$  is also connected. Finally, since Bers embedding is a continuous mapping (actually biholomorphic) and the closure of a connected set is connected, we conclude that  $\beta(T(1))\cap A_{2}(\mathbb{D})$  is connected in  $\beta(T(1))$ . ☐

COROLLARY 3.2. The Hilbert submanifold $T_0(1)$ of $T(1)$ is characterized by

$$
T _ {0} (1) = \{[ \mu ] \in T (1): \beta ([ \mu ]) \in A _ {2} (\mathbb {D}) \}.
$$

Next we prove that the Hilbert manifold $T_0(1)$ is a topological group.

LEMMA 3.3. Every $[\mu] \in T_0(1)$ has a representative $\mu \in L^2(\mathbb{D}^*, \rho(z)d^2z) \cap \mathcal{O}(\mathbb{D}^*)_1$.

PROOF. First observe that $L^2(\mathbb{D}^*, \rho(z)d^2z) \cap \mathcal{O}(\mathbb{D}^*)_1$ is a subgroup of $L^\infty(\mathbb{D}^*)_1$. Indeed, let $\lambda, \nu \in L^2(\mathbb{D}^*, \rho(z)d^2z) \cap \mathcal{O}(\mathbb{D}^*)_1$. Setting $\mu = \nu^{-1}$ and $\lambda_1 = \lambda, \lambda_2 = \nu$ in Lemma 2.7, we get

$$
\| \lambda * \nu^ {- 1} \| _ {2} <   C \| \lambda - \nu \| _ {2} <   \infty .
$$

Denote by $B_{\alpha}$ the ball of radius $\alpha$ about the origin in $A_2(\mathbb{D})$, where $\alpha < \sqrt{\frac{\pi}{3}}\delta$ and $\delta$ is defined in Corollary 2.6, and let $W_0 = (\Phi \circ \Lambda)(\beta (V_0)\cap B_\alpha)$. By definition, $W_{0}\subset T_{0}(1)$ and every $[\mu ]\in W_0$ has a representative $\mu \in L^{2}(\mathbb{D}^{*},\rho (z)d^{2}z)\cap \mathcal{O}(\mathbb{D}^{*})_{1}$. For every $\nu \in L^{\infty}(\mathbb{D}^{*})_{1}$ set $W_{\nu} = R_{[\nu]}(W_0)$.

For every $[\mu] \in T_0(1)$ let $[0,1] \ni t \mapsto [\mu(t)] \in T_0(1)$ be a path in $T_0(1)$ joining 0 to $[\mu]$. By definition of the Hilbert manifold structure on $T(1)$ (see Section 2.3), there exist $0 = t_0 < t_1 < \ldots < t_n = 1$ and $W_i = W_{\mu(t_i)} \subset T_0(1)$, which cover the path and such that $W_{i-1} \cap W_i \neq \emptyset$, $i = 1, \ldots, n$. We will prove by induction that each $[\mu(t_i)]$ has a representative $\mu_i \in L^2(\mathbb{D}^*, \rho(z)d^2z) \cap \mathcal{O}(\mathbb{D}^*)_1$. For $1 \leq i \leq n$, choose $[\nu_i] \in W_{i-1} \cap W_i$. Since $[\nu_1] \in W_0$, it has a representative $\nu_1 \in L^2(\mathbb{D}^*, \rho(z)d^2z) \cap \mathcal{O}(\mathbb{D}^*)_1$. On the other hand, since $[\nu_1] \in W_1$, $[\nu_1] = [\lambda * \mu(t_1)]$ for some $\lambda \in L^2(\mathbb{D}^*, \rho(z)d^2z) \cap \mathcal{O}(\mathbb{D}^*)_1$. Hence $[\mu(t_1)]$ has a representative $\mu_1 = \lambda^{-1} * \nu_1 \in L^2(\mathbb{D}^*, \rho(z)d^2z) \cap \mathcal{O}(\mathbb{D}^*)_1$. Now suppose that $[\mu(t_{i-1})]$ has a representative $\mu_{i-1} \in L^2(\mathbb{D}^*, \rho(z)d^2z) \cap \mathcal{O}(\mathbb{D}^*)_1$. Since $[\nu_i] \in W_{i-1} \cap W_i$, there exist $[\lambda_1], [\lambda_2] \in W_0$ such that $[\nu_i] = [\lambda_1 * \mu(t_{i-1})] = [\lambda_2 * \mu(t_i)]$. From the first equality it follows that $[\nu_i]$ has a representative $\nu_i \in L^2(\mathbb{D}^*, \rho(z)d^2z) \cap \mathcal{O}(\mathbb{D}^*)_1$, and the second equality implies that $[\mu(t_i)]$ has a representative $\mu_i \in L^2(\mathbb{D}^*, \rho(z)d^2z) \cap \mathcal{O}(\mathbb{D}^*)_1$. The assertion follows.

LEMMA 3.4. $T_0(1)$ is a subgroup of $T(1)$.

PROOF. Every $[\lambda] \in T_0(1)$ has a representative $\lambda \in L^2(\mathbb{D}^*, \rho(z)d^2z) \cap \mathcal{O}(\mathbb{D}^*)_1$. Using Lemma 2.9 with $\mu = \lambda^{-1}$ we get by Corollary 3.2 that $[\lambda^{-1}] \in T_0(1)$. Now let $[\nu] \in T_0(1)$ with a representative $\nu \in L^2(\mathbb{D}^*, \rho(z)d^2z) \cap \mathcal{O}(\mathbb{D}^*)_1$. Using again Lemma 2.9 with $\mu = \nu$ we get that $[\lambda * \nu] \in T_0(1)$.

The following lemmas and corollary are needed for the proof that $T_0(1)$ is a topological group. For every $[\mu] \in T(1)$ let

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026for download from IP 130.34.46.51.

$$
L _ {[ \mu ]}: T (1) \to T (1), \quad [ \nu ] \mapsto [ \mu * \nu ],
$$

be the left translation by $[\mu]$.

<!-- page 43 of 136 -->

34

1. CURVATURE PROPERTIES AND CHERN FORMS

LEMMA 3.5. Left translations are continuous on $T_0(1)$.

PROOF. Let $[\mu], [\kappa] \in T_0(1)$ with representatives $\mu, \kappa \in L^2(\mathbb{D}^*, \rho(z)d^2z) \cap \mathcal{O}(\mathbb{D}^*)_1$, and let $V_\kappa$ and $V_{\mu*\kappa}$ be coordinate charts introduced in Section 2.3. In terms of corresponding Bers coordinates the mapping $L_{[\mu]}$ takes the form

$$
\beta \circ \Phi \circ R _ {(\mu * \kappa) ^ {- 1}} \circ L _ {\mu} \circ R _ {\kappa} \circ \Lambda : \beta (V _ {0}) \subset A _ {2} (\mathbb {D}) \to A _ {2} (\mathbb {D}).
$$

Since left translations commute with right translations, it simplifies to

$$
\beta \circ \Phi \circ R _ {\mu^ {- 1}} \circ L _ {\mu} \circ \Lambda : \beta (V _ {0}) \subset A _ {2} (\mathbb {D}) \to A _ {2} (\mathbb {D}),
$$

which does not depend on $[\kappa]$. Thus to show that $L_{[\mu]}$ is continuous at $[\kappa] \in T_0(1)$ it is sufficient to show that the above mapping is continuous at $0 \in A_2(\mathbb{D})$. From Lemma 2.7 it follows that the mapping

$$
R _ {\mu^ {- 1}}: L ^ {2} (\mathbb {D} ^ {*}, \rho (z) d ^ {2} z) \cap L ^ {\infty} (\mathbb {D} ^ {*}) _ {1} \to L ^ {2} (\mathbb {D} ^ {*}, \rho (z) d ^ {2} z) \cap L ^ {\infty} (\mathbb {D} ^ {*}) _ {1}
$$

is continuous at $\mu$, and from Lemma 2.9 it follows that the mapping

$$
\beta \circ \Phi : L ^ {2} (\mathbb {D} ^ {*}, \rho (z) d ^ {2} z) \cap L ^ {\infty} (\mathbb {D} ^ {*}) _ {1} \to A _ {2} (\mathbb {D})
$$

is continuous at 0. What remains to show is that the mapping

$$
\begin{array}{c} L _ {\mu}: H ^ {- 1, 1} (\mathbb {D} ^ {*}) \cap L ^ {\infty} (\mathbb {D} ^ {*}) _ {1} \to L ^ {2} (\mathbb {D} ^ {*}, \rho (z) d ^ {2} z), \\ \nu \mapsto \mu * \nu = \frac {(\mu \circ w _ {\nu}) \overline {{\frac {(w _ {\nu}) _ {z}}{(w _ {\nu}) _ {z}}}} + \nu}{1 + (\mu \circ w _ {\nu}) \bar {\nu} \overline {{\frac {(w _ {\nu}) _ {z}}{(w _ {\nu}) _ {z}}}}} \end{array}
$$

is continuous at 0.

For $\nu \in H^{-1,1}(\mathbb{D}^*)\cap L^{\infty}(\mathbb{D}^{*})_{1}$ we have

$$
L _ {\mu} (\nu) - L _ {\mu} (0) = \frac {(\mu \circ w _ {\nu}) \overline {{\frac {(w _ {\nu}) _ {z}}{(w _ {\nu}) _ {z}}}} - \mu + \nu - (\mu \circ w _ {\nu}) \mu \bar {\nu} \overline {{\frac {(w _ {\nu}) _ {z}}{(w _ {\nu}) _ {z}}}}}{1 + (\mu \circ w _ {\nu}) \bar {\nu} \overline {{\frac {(w _ {\nu}) _ {z}}{(w _ {\nu}) _ {z}}}}}.
$$

Since $\mu \in L^{2}(\mathbb{D}^{*},\rho (z)d^{2}z)$, for every $\varepsilon >0$ there exists $0 < r < 1$ such that

$$
\left| \iint_ {\mathbb {D} \backslash \mathbb {D} _ {r}} | \mu | ^ {2} \rho (z) d ^ {2} z <   \frac {\varepsilon^ {2}}{1 6}. \right|
$$

It follows from Mori's theorem (see, e.g., [Ahl87]) that for every $0 < \delta_1 < 1$ there exists $0 < r_0 < 1$ such that for all $\| \nu \|_{\infty} < \delta_1$ and $r_0 \leq r < 1$,

$$
w _ {\nu} (\mathbb {D} \setminus \mathbb {D} _ {r ^ {\prime}}) \subset \mathbb {D} \setminus \mathbb {D} _ {r}, \quad \text {for all} \quad r ^ {\prime} \geq \frac {1 + r}{2}.
$$

Hence if $\| \nu \|_{\infty} < \min \{\delta, \delta_1\}$, where $\delta$ is as in Corollary 2.6, we have

$$
\begin{array}{r l} & {\left| \iint_ {\mathbb {D}} \left| \mu \circ w _ {\nu} \frac {\overline {{(w _ {\nu}) _ {z}}}}{(w _ {\nu}) _ {z}} - \mu \right| ^ {2} \rho (z) d ^ {2} z \leq 2 \iint_ {\mathbb {D} \setminus \mathbb {D} _ {r ^ {\prime}}} \left| \mu \circ w _ {\nu} \frac {\overline {{(w _ {\nu}) _ {z}}}}{(w _ {\nu}) _ {z}} \right| ^ {2} \rho (z) d ^ {2} z \right|} \\ & {\qquad + 2 \iint_ {\mathbb {D} \setminus \mathbb {D} _ {r ^ {\prime}}} | \mu | ^ {2} \rho (z) d ^ {2} z + \iint_ {\mathbb {D} _ {r ^ {\prime}}} \left| \mu \circ w _ {\nu} \frac {\overline {{(w _ {\nu}) _ {z}}}}{(w _ {\nu}) _ {z}} - \mu \right| ^ {2} \rho (z) d ^ {2} z} \\ & {\qquad \leq \frac {3 \varepsilon^ {2}}{8} + \iint_ {\mathbb {D} _ {r ^ {\prime}}} \left| \mu \circ w _ {\nu} \frac {\overline {{(w _ {\nu}) _ {z}}}}{(w _ {\nu}) _ {z}} - \mu \right| ^ {2} \rho (z) d ^ {2} z.} \end{array}
$$

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

<!-- page 44 of 136 -->

3. $T_{0}(1)$ AS A TOPOLOGICAL GROUP

35

Since $w_{\nu}(z) \to z$, $(w_{\nu})_z(z) \to 1$ as $\| \nu \|_{\infty} \to 0$ uniformly for all $z \in \mathbb{D}_{r'}$, we can choose $\delta_2$ such that for all $\| \nu \|_{\infty} < \delta_2$, the second integral is less than $\frac{\varepsilon^2}{8}$. Finally, let $\delta_3 \leq \sqrt{\frac{4\pi}{3}} \min \{\delta, \delta_1, \delta_2\}$, then for all $\| \nu \|_2 < \delta_3$, we have

$$
\left\| L _ {\mu} (\nu) - L _ {\mu} (0) \right\| _ {2} <   \frac {1}{1 - \sqrt {\frac {3}{4 \pi}} \delta_ {3}} \left(\frac {\varepsilon}{\sqrt {2}} + 2 \delta_ {3}\right),
$$

which is less than $\varepsilon$ for $\delta_3$ sufficiently small.

Notice that what we actually prove is the following

COROLLARY 3.6. For every $[\mu] \in T_0(1)$ the adjoint mapping

$$
T _ {0} (1) \ni [ \nu ] \mapsto [ \mu * \nu * \mu^ {- 1} ] \in T _ {0} (1)
$$

is continuous at the origin.

LEMMA 3.7. The following statements hold.

(i) The inverse mapping $T_0(1) \ni [\mu] \mapsto [\mu^{-1}] \in T_0(1)$ is continuous at the origin.

(ii) The group multiplication $T_0(1) \times T_0(1) \ni ([\mu], [\nu]) \mapsto [\mu * \nu] \in T_0(1)$ is continuous at the origin.

PROOF. In coordinate chart $V_{0}$ the inverse mapping takes the form

$$
A _ {2} (\mathbb {D}) \supset \beta (V _ {0}) \ni \phi \mapsto \beta \circ \Phi ((\Lambda \phi) ^ {- 1}) \in A _ {2} (\mathbb {D}).
$$

By Lemma 2.9, it is continuous at 0. This proves (i). In coordinate chart $V_{0}$ the group multiplication takes the form

$$
\beta (V _ {0}) \times \beta (V _ {0}) \ni (\phi_ {1}, \phi_ {2}) \mapsto \beta \circ \Phi (\Lambda (\phi_ {1}) * \Lambda (\phi_ {2})) \in A _ {2} (\mathbb {D}).
$$

Its continuity at $(0,0)\in A_2(\mathbb{D})\times A_2(\mathbb{D})$ follows from Lemma 2.9 and the proof of Lemma 3.5.

THEOREM 3.8. The Hilbert manifold $T_0(1)$ is a topological group.

PROOF. We need to prove that the map

$$
T _ {0} (1) \times T _ {0} (1) \ni ([ \mu ], [ \nu ]) \mapsto [ \mu * \nu^ {- 1} ] \in T _ {0} (1)
$$

is continuous at every point $([ \mu ], [\nu]) \in T_0(1) \times T_0(1)$ with representatives $\mu, \nu \in L^2(\mathbb{D}^*, \rho(z)d^2z) \cap \mathcal{O}(\mathbb{D}^*)_1$. In coordinate charts $V_\mu$, $V_\nu$ and $V_\kappa$, where $\kappa = \mu * \nu^{-1}$, this map takes the form

$$
\beta (V _ {0}) \times \beta (V _ {0}) \ni (\phi_ {1}, \phi_ {2}) \mapsto \beta \circ \Phi (\Lambda (\phi_ {1}) * \kappa * \Lambda (\phi_ {2}) ^ {- 1} * \kappa^ {- 1}) \in A _ {2} (\mathbb {D}).
$$

Its continuity at $(0,0)\in A_2(\mathbb{D})\times A_2(\mathbb{D})$ follows from Corollary 3.6, Lemma 3.7 and Lemma 2.9.

Finally, we show that $\mathcal{T}_0(1)$ is also a topological group.

PROPOSITION 3.9. The Hilbert manifold $\mathcal{T}_0(1)$ is a topological group.

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026for download from IP 130.34.46.51.

<!-- page 45 of 136 -->

36

1. CURVATURE PROPERTIES AND CHERN FORMS

PROOF. We have to prove that the multiplication map

$$
\mathcal {T} _ {0} (1) \times \mathcal {T} _ {0} (1) \ni (\gamma_ {1}, \gamma_ {2}) \mapsto \gamma_ {1} * \gamma_ {2} ^ {- 1} \in \mathcal {T} _ {0} (1)
$$

is continuous. Setting $\gamma_{1} = ([\nu],\zeta)$ and $\gamma_{2} = ([\mu],w)$, we get from (1.13) that $\gamma_1*\gamma_2^{-1} = ([\lambda ],z)$, where

$$
\lambda = (\sigma_ {u} ^ {- 1}) ^ {*} (\nu * \mu^ {- 1}), \quad z = (w ^ {\lambda} \circ \gamma_ {1} \circ (w ^ {\nu}) ^ {- 1}) (\zeta),
$$

and

$$
\gamma_ {2} = \sigma_ {u} \circ w _ {\mu} = g _ {\mu} ^ {- 1} \circ f ^ {\mu}, \quad u = g _ {\mu} ^ {- 1} (w).
$$

It easily follows from the proof of Lemma 3.5 that the mapping

$$
\operatorname{Möb} (S ^ {1}) \times T (1) \ni (\sigma , [ \mu ]) \mapsto [ (\sigma^ {- 1}) ^ {*} (\mu) ] \in T (1)
$$

is continuous. Now the map $\mathcal{T}(1) \ni ([\mu], w) \mapsto g_{\mu}^{-1}(w) \in \mathbb{D}^*$ depends continuously on $[\mu]$ (uniformly when $w$ varies on compact subsets), so using that $T_0(1)$ is a topological group, we conclude that $[\lambda] \in T_0(1)$ depends continuously on $\gamma_1, \gamma_2 \in \mathcal{T}_0(1)$. Finally, by the result of Bers [Ber73] (which we already have used in the proof of Lemma 5.4) we get that $z \in \mathbb{D}^*$ also depends continuously on $\gamma_1$ and $\gamma_2$.

## 4. Velling-Kirillov and Weil-Petersson metrics

4.1. Velling-Kirillov metric on the universal Teichmüller curve. The Velling-Kirillov metric is a right-invariant Hermitian metric on  $\mathcal{T}(1)$ , defined at the origin of  $\mathcal{T}(1)$  by

$$
\left| \| \mathrm{v} \| _ {V K} ^ {2} = \sum_ {n = 1} ^ {\infty} n \left| c _ {n} \right| ^ {2}, \right.\tag{4.1}
$$

where

$$
\left| \mathrm{v} = \frac {\mathrm{u} - i J \mathrm{u}}{2} \quad \text {and} \quad \mathrm{u} = \sum_ {n \in \mathbb {Z} \backslash \{0 \}} c _ {n} e ^ {i n \theta} \frac {d}{d \theta} \in T _ {0} ^ {\mathbb {R}} S ^ {1} \backslash \operatorname{Homeo} _ {q s} (S ^ {1}). \right.
$$

The convergence of the series is guaranteed by the property TS4 (with s = 1/2) in Section 1.2.3. The Velling-Kirillov metric is a smooth right-invariant Kähler metric on the complex Banach manifold  $\mathcal{T}(1)$ . Its symplectic form  $\omega_{VK}$  at the origin of  $\mathcal{T}(1)$  is given by

$$
\omega_ {V K} (\mathrm{v}, \bar {\mathrm{v}}) = \frac {i}{2} \| \mathrm{v} \| _ {V K} ^ {2},
$$

In the following section we prove that the Velling-Kirillov metric is real-analytic on $\mathcal{T}(1)$ by presenting its real-analytic Kähler potential.

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026for download from IP 130.34.46.51.

REMARK 4.1. For the homogeneous space $S^1 \setminus \mathrm{Diff}_+(S^1)$ the metric was introduced in this form by A.A. Kirillov [Kir87] and it has been studied by A.A. Kirillov and D. Yuriev. In particular, in [KY87] it was shown to be Kähler. In [Vel], J. Velling has introduced a Hermitian metric for the space $\mathcal{T}(1)$ using arguments from geometric function theory. In [Teo04], Kirillov's definition was extended to $\mathcal{T}(1)$ and it was shown that the resulting metric coincides with the metric introduced by Velling. The Velling-Kirillov metric is the unique right-invariant Kähler metric on the universal Teichmüller curve $\mathcal{T}(1)$ [Teo04].

<!-- page 46 of 136 -->

4. VELLING-KIRILLOV AND WEIL-PETERSSON METRICS

37

4.2. Weil-Petersson metric on the universal Teichmüller space. In this section we consider $T(1)$ as a Hilbert manifold. The Weil-Petersson metric on $T(1)$ is a Hermitian metric defined by the Hilbert space inner product on tangent spaces, which are identified with the Hilbert space $H^{-1,1}(\mathbb{D}^*)$ by right translations (see Section 2.3). Thus the Weil-Petersson metric is a right-invariant metric on $T(1)$ defined at the origin of $T(1)$ by

$$
\langle \mu , \nu \rangle_ {W P} = \iint_ {\mathbb {D} ^ {*}} \mu \bar {\nu} \rho (z) d ^ {2} z, \mu , \nu \in H ^ {- 1, 1} (\mathbb {D} ^ {*}) = T _ {0} T (1).\tag{4.2}
$$

To every $\mu \in H^{-1.1}(\mathbb{D}^*)$ there corresponds a vector field $\frac{\partial}{\partial\varepsilon_{\mu}}$ over $V_0$, given by (1.5)-(1.7). We set for every $\kappa \in V_0$,

$$
g _ {\mu \bar {\nu}} (\kappa) = \left\langle \left. \frac {\partial}{\partial \varepsilon_ {\mu}} \right| _ {\kappa}, \left. \frac {\partial}{\partial \varepsilon_ {\nu}} \right| _ {\kappa} \right\rangle_ {W P} = \iint_ {\mathbb {D} ^ {*}} P (R (\mu , \kappa)) \overline {{P (R (\nu , \kappa))}} \rho (z) d ^ {2} z.\tag{4.3}
$$

This formula explicitly defines the Weil-Petersson metric on the coordinate chart $V_{0}$. The Weil-Petersson metric extends to other charts $V_{\mu}$ by right translations.

The following statement is an easy consequence of Lemma 2.5.

LEMMA 4.2. The Weil-Petersson metric is continuous on $T(1)$.


> **[ERRATUM 3-20]** (TT:2170–2186; Lean: `lemma_4_2` (S4)) **proof gap** (statement true). The displayed bound of ` \| g(κ) - g(0) \| ` does not follow: `g(κ) ≤ ‖R(μ,κ)‖²` only bounds `g(κ)` from above, and the difference compares `‖P R(μ,κ)‖²` with `‖μ‖²`, which needs `R(μ,κ) → μ` in `L²(ρ)` (continuity of `κ ↦ R(μ,κ)`, incl. the phase `w_z/\overline{w_z}`), not only Lemma 2.5's modulus bound (found by 下属1, R1 triage)

PROOF. As it follows from Corollary 2.12, it is sufficient to prove that for every $\mu \in H^{-1,1}(\mathbb{D}^*)$ the function $g_{\mu \bar{\mu}}$ is continuous on $V_0$ at 0. Since the embedding $V_0 \hookrightarrow U_0$ is continuous by Lemma 2.1, it is sufficient to prove that the function $g_{\mu \bar{\mu}}$ is defined on a neighborhood of 0 in $U_0$ and is continuous at 0.

Since the projector $P$ is norm-decreasing,

$$
\begin{array}{l} g _ {\mu \bar {\mu}} (\kappa) = \iint_ {\mathbb {D} ^ {*}} P (R (\mu , \kappa)) \overline {{P (R (\mu , \kappa))}} \rho (z) d ^ {2} z \\ \qquad \leq \iint_ {\mathbb {D} ^ {*}} R (\mu , \kappa) \overline {{R (\mu , \kappa)}} \rho (z) d ^ {2} z \\ \qquad = 4 \iint_ {\mathbb {D} ^ {*}} \frac {| \mu | ^ {2}}{1 - | \kappa | ^ {2}} \frac {| (w _ {\kappa}) _ {z} | ^ {2}}{(1 - | w _ {\kappa} | ^ {2}) ^ {2}} d ^ {2} z. \end{array}
$$

According to Lemma 2.5, for every $\varepsilon > 0$ there exists $0 < \delta < 1$ such that for all $\kappa \in U_0$ satisfying $\| \kappa \|_{\infty} < \delta$ we have

$$
\begin{array}{c} \left| g _ {\mu \bar {\mu}} (\kappa) - g _ {\mu \bar {\mu}} (0) \right| \leq 4 \iint_ {\mathbb {D} ^ {*}} \frac {| \mu | ^ {2}}{1 - | \kappa | ^ {2}} \left| \frac {| (w _ {\kappa}) _ {z} | ^ {2}}{(1 - | w _ {\kappa} | ^ {2}) ^ {2}} - \frac {1}{(1 - | z | ^ {2}) ^ {2}} \right| \\ \qquad \qquad + \frac {| \mu | ^ {2}}{(1 - | z | ^ {2}) ^ {2}} \left(\frac {1}{1 - | \kappa | ^ {2}} - 1\right) d ^ {2} z \\ \leq \frac {\varepsilon + \delta^ {2}}{1 - \delta^ {2}} \iint_ {\mathbb {D}} | \mu | ^ {2} \rho d ^ {2} z. \end{array}
$$

Thus, for $\delta$ small enough $\left|g_{\mu \bar{\mu}}(\kappa) - g_{\mu \bar{\mu}}(0)\right|\leq 2\varepsilon \| \mu \|_2^2$.

REMARK 4.3. Using the basic properties of the q.c. mappings, it can be shown that the Weil-Petersson metric is real-analytic on $T(1)$. In fact, it is sufficient to

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026for download from IP 130.34.46.51.

<!-- page 47 of 136 -->

38

1. CURVATURE PROPERTIES AND CHERN FORMS

prove that for every $\mu, \nu \in H^{-1.1}(\mathbb{D}^*)$ the mapping $V_0 \ni \kappa \mapsto g_{\mu \bar{\nu}}(\kappa) \in \mathbb{C}$ is real-analytic on $V_0$. Since this result will not be used later, we omit the proof. Explicit curvature computations in Section 7 will show that the Weil-Petersson metric on $T(1)$ is twice differentiable.

We will prove in Section 7 that the Weil-Petersson metric is Kähler. Its symplectic form $\omega_{WP}$ is a right-invariant (1,1) form on the Hilbert manifold $T(1)$. At the origin of $T(1)$,

$$
\omega_ {W P} (\mu , \bar {\nu}) = \frac {i}{2} \langle \mu , \nu \rangle_ {W P}, \mu , \nu \in H ^ {- 1, 1} (\mathbb {D} ^ {*}).
$$

REMARK 4.4. The Weil-Petersson metric on the distribution $\mathfrak{D}_T$ (without defining the Hilbert manifold structure) was introduced by S. Nag and A. Verjovsky [NV90] as a direct generalization of the Weil-Petersson metric on the finite-dimensional Teichmüller spaces. It was proved in [NV90] that the embedding $\mathrm{Möb}(S^1)\backslash \mathrm{Diff}_+(S^1)\hookrightarrow T(1)$ is holomorphic and the pull-back of the Weil-Petersson metric on the distribution $\mathfrak{D}_T$ coincides, up to a constant, with the right invariant Kähler metric introduced by Kirillov [Kir87] by the orbit method. At the tangent space of the origin the latter metric is defined by (cf. (4.1))

$$
\left\| \mathrm{v} \right\| ^ {2} = \sum_ {n = 2} ^ {\infty} (n ^ {3} - n) | c _ {n} | ^ {2},
$$

where

$$
\mathrm{v} = \frac {\mathrm{u} - i J \mathrm{u}}{2} \quad \text {and} \quad \mathrm{u} = \sum_ {n \in \mathbb {Z} \backslash \{0, \pm 1 \}} c _ {n} e ^ {i n \theta} \frac {d}{d \theta} \in T _ {0} ^ {\mathbb {R}} \operatorname{Mob} (S ^ {1}) \backslash \operatorname{Diff} _ {+} (S ^ {1}).
$$

## 5. Characteristic forms of the universal Teichmüller curve

Let $V = T_{v}\mathcal{T}(1)$ be the vertical tangent bundle of the fibration

$$
\pi : \mathcal {T} (1) \to T (1).
$$

It is a holomorphic line bundle over the complex Banach manifold $\mathcal{T}(1)$, the fiber over a point $([\mu], z) \in \mathcal{T}(1)$ is the holomorphic tangent bundle to the quasi-disk $w^{\mu}(\mathbb{D}^{*})$. The hyperbolic metric on $w^{\mu}(\mathbb{D}^{*})$ defines a Hermitian metric on $V$, and we denote by $c_{1}(V)$ the first Chern form of $V$ corresponding to this metric.

The Hilbert manifold structure on $T(1)$ naturally induces a Hilbert manifold structure on $\mathcal{T}(1)$, such that the projection $\pi : \mathcal{T}(1) \to T(1)$ is a holomorphic mapping of Hilbert manifolds. Similar to the Hilbert manifold $T(1)$, the Hilbert manifold $\mathcal{T}(1)$ is also a disjoint union of uncountably many components. We will prove in Appendix A that the component containing the identity $\mathcal{T}_0(1)$ is a topological group.

The vertical tangent bundle is also a holomorphic line bundle over the Hilbert manifold $\mathcal{T}(1)$. We will continue to denote corresponding line bundle by $V$, and by $c_{1}(V)$ — the first Chern form corresponding to the hyperbolic metric on the fibers, specifying explicitly which topology we are using. Since the Hilbert manifold topology is stronger than the Banach manifold topology, the form $c_{1}(V)$ for the Banach manifold structure on $\mathcal{T}(1)$ naturally restricts onto $\mathcal{T}(1)$ considered as a Hilbert manifold.

Similar to Wolpert's work [Wol86] on finite dimensional Teichmüller spaces, we define the analogs of Mumford-Morita-Miller characteristic forms as the following

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026for download from IP 130.34.46.51.

<!-- page 48 of 136 -->

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026for download from IP 130.34.46.51.

5. CHARACTERISTIC FORMS OF THE UNIVERSAL TEICHMÜLLER CURVE

39

$(n,n)$-forms on the Hilbert manifold $T(1)$,

$$
\kappa_ {n} = (- 1) ^ {n + 1} \pi_ {*} (c _ {1} (V) ^ {n + 1}),\tag{5.1}
$$

where  $\pi_{*}:\Omega^{*}(\mathcal{T}(1))\to\Omega^{*-2}(T(1))$  is the operation of “integration over the fibers” of the fibration  $\pi:\mathcal{T}(1)\to T(1)$ . As we will see in Section 5.3, it is the passage from the Banach manifold structure to the Hilbert manifold structure that makes the operation  $\pi_{*}$  well-defined (i.e., the integrals over non-compact fibers become convergent).

5.1. The form $c_{1}(V)$ as Velling-Kirillov symplectic form. In this section we work with the Banach manifold structure on $\mathcal{T}(1)$. Let $z$ be the complex coordinate on $\hat{\mathbb{C}} \setminus \{0\}$. The assignment $\mathcal{T}(1) \ni ([\mu], z) \mapsto -z^{2}\partial_{z}$ defines a holomorphic section of the line bundle $V$ over $\mathcal{T}(1)^{4}$. The hyperbolic metric on $w^{\mu}(\mathbb{D}^{*})$ is the pull-back of the hyperbolic metric on $\mathbb{D}^{*}$ by the conformal map $g_{\mu}^{-1}$, so that

$$
\left\| z ^ {2} \partial_ {z} \right\| _ {([ \mu ], z)} ^ {2} = \frac {4 | z ^ {2} (g _ {\mu} ^ {- 1}) ^ {\prime} (z) | ^ {2}}{(| g _ {\mu} ^ {- 1} (z) | ^ {2} - 1) ^ {2}}.
$$

The first Chern form of the line bundle $V$ is

$$
c _ {1} (V) = \frac {i}{2 \pi} \Theta = \frac {i}{2 \pi} \bar {\partial} \partial \log \left\| z ^ {2} \partial_ {z} \right\| ^ {2},
$$

where $\partial$ and $\bar{\partial}$ are, respectively, the (1,0) and (0,1) components of the de Rham differential on $\mathcal{T}(1)$.

Let

$$
K = \log \left\| z ^ {2} \partial_ {z} \right\| _ {([ \mu ], z)} - \log 2.
$$

LEMMA 5.1. The function $K: \mathcal{T}(1) \to \mathbb{R}$ is real-analytic. Under the correspondence $\mathcal{T}(1) \ni ([\mu], z) \mapsto \mathrm{g} \in S^1 \backslash Homeo_{qs}(S^1)$, where $\gamma = (g^{-1} \circ f)\big|_{S^1}$,

$$
K (\gamma) = \log | g ^ {\prime} (\infty) |.
$$

PROOF. Using the formulas $g = \lambda_w \circ g_\mu \circ \sigma_w^{-1}$ and $w = g_\mu^{-1}(z)$ from Section 1.2.1, it is straightforward to compute

$$
g ^ {\prime} (\infty) = \frac {z ^ {2} (g _ {\mu} ^ {- 1}) ^ {\prime} (z) (1 - \bar {w})}{(| w | ^ {2} - 1) (1 - w)}.
$$

Now it easily follows from the general properties of q.c. mappings that for $z \in \mathbb{D}^*$ the functional $T(1) \ni [\mu] \mapsto g_{\mu}^{-1}(z) \in \mathbb{C}$ is real-analytic so that $|g'(\infty)|$ is a real-analytic function on $\mathcal{T}(1)$.

REMARK 5.2. The quantity $|g'(\infty)|$ is the capacity of the quasi-circle $g(S^1)$ corresponding to $\gamma \in \mathrm{Homeo}_{qs}(S^1)$.

THEOREM 5.3. The first Chern form of the vertical tangent bundle to the universal Teichmüller curve $\mathcal{T}(1)$ is proportional to the symplectic form of the Velling-Kirillov metric,

$$
c _ {1} (V) = - \frac {2}{\pi} \omega_ {V K}.
$$

Equivalently, the function $K$ is a Kähler potential for the Velling-Kirillov metric on $\mathcal{T}(1)$.

PROOF. It is based on the following lemmas.

<small><span class="docvortex-page-footnote" data-block-type="page_footnote" style="color:#6b7280">$z\mapsto\frac{1}{z}$</span></small>

<small><span class="docvortex-page-footnote" data-block-type="page_footnote" style="color:#6b7280">$-z^{2}\partial_{z}\mapsto\partial_{z}$</span></small>

<small><span class="docvortex-page-footnote" data-block-type="page_footnote" style="color:#6b7280">$^{4}$ Under the conformal map  $z \mapsto \frac{1}{z}$  the vector field  $-z^{2}\partial_{z} \mapsto \partial_{z}$ .</span></small>

<!-- page 49 of 136 -->

40

1. CURVATURE PROPERTIES AND CHERN FORMS

## LEMMA 5.4. The (1,1)-form $c_{1}(V)$ on $\mathcal{T}(1)$ is right-invariant.

PROOF. We need to prove that for every  $g_{0} \in S^{1} \backslash \text{Homeo}(S^{1}) \cong \mathcal{T}(1)$  the difference  $R_{\gamma_{0}}^{*} K - K$ , where  $R_{\gamma_{0}} : \mathcal{T}(1) \to \mathcal{T}(1)$  is the right translation by  $\gamma_{0}$  and  $(R_{\gamma_{0}}^{*} K)(\gamma) = K(\gamma \circ \gamma_{0})$ , is a harmonic function on  $\mathcal{T}(1)$ .

For every $\gamma = g^{-1} \circ f \in \mathcal{T}(1)$ let $\tilde{\gamma} = \gamma \circ \gamma_0 = \tilde{g}^{-1} \circ \tilde{f}$. Since $\tilde{g} = \tilde{f} \circ \mathrm{g}_0^{-1} \circ f^{-1} \circ g$, we have

$$
\left(R _ {\gamma_ {0}} ^ {*} K - K\right) (\gamma) = \log | \tilde {g} ^ {\prime} (\infty) | - \log | g ^ {\prime} (\infty) | = \log | (\tilde {f} \circ \gamma_ {0} ^ {- 1} \circ f ^ {- 1}) ^ {\prime} (\infty) |.
$$

In [Ber73], Bers has proved that the function

$$
(\gamma , z) \mapsto \left(\tilde {f} \circ \gamma_ {0} ^ {- 1} \circ f ^ {- 1}\right) (z) = h (\gamma , z)
$$

depends holomorphically on $\gamma$ and $z$, which implies that $\left(\tilde{f} \circ \gamma_0^{-1} \circ f^{-1}\right)'(\infty)$ depends holomorphically on $\gamma$ and our assertion follows.

LEMMA 5.5. Let $\gamma = g^{-1} \circ f \in \mathcal{T}(1)$, where $f|_{\mathbb{D}}(z) = \sum_{n=0}^{\infty} a_n z^{n+1}$, $a_0 = 1$, and $g|_{\mathbb{D}^*}(z) = \sum_{n=0}^{\infty} b_n z^{1-n}$. Then

$$
| b _ {0} | ^ {2} = \sum_ {n = 0} ^ {\infty} (n + 1) | a _ {n} | ^ {2} + \sum_ {n = 1} ^ {\infty} (n - 1) | b _ {n} | ^ {2}.\tag{5.2}
$$

PROOF. Evaluate the Euclidean area of the domain $\Omega = f(\mathbb{D}) = g(\mathbb{D})$ in two different ways. First,

$$
A _ {E} (\Omega) = \lim _ {r \to 1 ^ {-}} \iint_ {f (\mathbb {D} _ {r})} d ^ {2} z = \lim _ {r \to 1 ^ {-}} \iint_ {\mathbb {D} _ {r}} | f ^ {\prime} | ^ {2} d ^ {2} z = \pi \sum_ {n = 0} ^ {\infty} (n + 1) | a _ {n} | ^ {2},
$$


> **[IMPLICIT HYPOTHESIS 3-26]** (TT:2336–2346; Lean: `lemma_5_5` proof (S5)) equating the two areas needs `area(∂Ω) = 0`: true because `∂Ω` is a quasicircle (q.c. image of `S¹`), not said in TT

where $\mathbb{D}_r = \{z\in \mathbb{C}:|z| < r\}$. On the other hand, the classical area theorem gives

$$
\left| A _ {E} (\Omega) = \pi \sum_ {n = 0} ^ {\infty} (1 - n) | b _ {n} | ^ {2}, \right.
$$

and we obtain (5.2).

Now we complete the proof of the theorem. Let


> **[ERRATUM 3-27]** (TT:2349–2359; Lean: `eq_5_3_5_4` (S5)) OCR/print: the second term must be conjugated (as the docstring and TT's next display `b̈₀ + \bar b̈₀ + 2 \| ḃ₀ \| ²` show)
> **[IMPLICIT HYPOTHESIS 3-28]** (TT:2349–2390; Lean: `eq_5_3_5_4` (S5)) TT's termwise differentiation needs smoothness in the Hilbert manifold (control of the coefficient tail); with C² only on open sets clause 2 fails (sketch: `u = 0`, high-frequency wiggles `f^t = z + Σ ψ_k(t)(t/√N_k)z^{N_k}` give `(log \| b₀ \| )''(0) ≥ 1`). Clause 1 is fine as before

$$
\mathrm{u} = \sum_ {n \in \mathbb {Z} \backslash \{0 \}} c _ {n} e ^ {i n \theta} \frac {d}{d \theta} \in T _ {0} ^ {\mathbb {R}} \mathcal {T} (1),
$$

and let $\gamma_{t} = g_{t}^{-1}\circ f^{t}$, $\gamma_0 = \mathrm{id}$, be the corresponding smooth curve in $\mathcal{T}(1)$. Using notations from the previous lemma, differentiate the relation (5.2) with respect to $t$ and set $t = 0$, and using $b_{0}(0) = 1$, $a_{n}(0) = b_{n}(0) = 0$ for $n\geq 1$, we get

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

$$
\dot {b} _ {0} + \dot {b} _ {0} = 0.\tag{5.3}
$$

Here we denote

$$
\dot {a} _ {n} (\mathrm{u}) = \dot {a} _ {n} = \frac {d a _ {n}}{d t} (0) \quad \text {and} \quad \dot {b} _ {n} (\mathrm{u}) = \dot {b} _ {n} = \frac {d b _ {n}}{d t} (0).
$$

<!-- page 50 of 136 -->

5. CHARACTERISTIC FORMS OF THE UNIVERSAL TEICHMÜLLER CURVE

41

Differentiating (5.2) twice with respect to $t$ and setting $t = 0$ we get

$$
\begin{array}{c} \frac {d ^ {2} b _ {0}}{d t ^ {2}} (0) + \frac {d ^ {2} \bar {b} _ {0}}{d t ^ {2}} (0) + 2 \left| \frac {d b _ {0}}{d t} (0) \right| ^ {2} = 2 \sum_ {n = 1} ^ {\infty} (n + 1) | \dot {a} _ {n} | ^ {2} + 2 \sum_ {n = 1} ^ {\infty} (n - 1) | \dot {b} _ {n} | ^ {2} \\ = 4 \sum_ {n = 1} ^ {\infty} n | \dot {a} _ {n} | ^ {2}, \end{array}
$$

where we have also used the property TS1 in Section 1.2.3. Since $g_{t}^{\prime}(\infty) = b_{0}(t)$, using (5.3) we get


> **[ERRATUM 3-29]** (TT:2380–2386; Lean: `eq_5_3_5_4` second-variation display (S5)) OCR: the outer ` \| … \| ` is a misread evaluation bar `… \| _{t=0}`

$$
\left| \frac {d ^ {2}}{d t ^ {2}} \log | g _ {t} ^ {\prime} (\infty) | \right| _ {t = 0} = 2 \sum_ {n = 1} ^ {\infty} n | \dot {a} _ {n} | ^ {2}.
$$

Let $\mathrm{v} = \frac{1}{2} (\mathrm{u} - iJ\mathrm{u})$ be the holomorphic tangent vector to $\mathcal{T}(1)$. Since $\dot{a}_n(J\mathrm{u}) = i\dot{a}_n(\mathrm{u})$, using (1.16) we finally get

$$
(\partial \bar {\partial} K) (\mathrm{v}, \bar {\mathrm{v}}) = \frac {1}{2} \sum_ {n = 1} ^ {\infty} n \left(| \dot {a} _ {n} (\mathrm{u}) | ^ {2} + | \dot {a} _ {n} (J \mathrm{u}) | ^ {2}\right) = \sum_ {n = 1} ^ {\infty} n | \dot {a} _ {n} (\mathrm{u}) | ^ {2}.\tag{5.4}
$$

This proves that $\Theta = 4i\omega_{VK}$ at the origin of $\mathcal{T}(1)$. Since both these (1,1)-forms on $\mathcal{T}(1)$ are right-invariant, the assertion follows.

REMARK 5.6. In [KY87], A.A. Kirillov and D. Yuriev have stated that the function K, restricted to the space  $S^{1} \backslash \text{Diff}_{+}(S^{1})$ , is a Kähler potential of the Velling-Kirillov metric. Theorem 5.3 extends this result to  $\mathcal{T}(1) \simeq S^{1} \backslash \text{Homeo}_{qs}(S^{1})$  and gives its geometric interpretation.

5.2. The Chern form $c_{1}(V)$ and the resolvent kernel. Let $\mu \in \Omega^{-1,1}(\mathbb{D}^{*})$ be a horizontal holomorphic tangent vector to $\mathcal{T}(1)$ at the origin. According to the property TV1 in Section 1.2.2, the vector field $\tau_{\mu}$ — the horizontal lift of the vector field $\frac{\partial}{\partial\varepsilon_{\mu}}$ on $U_0 \subset T(1)$ to the point $(0,z) \in \pi^{-1}(0)$, is identified with $(\sigma_z^{-1})^*\mu \in \Omega^{-1,1}(\mathbb{D}^*)$.

PROPOSITION 5.7. (i) On the fiber $\pi^{-1}(0)\subset \mathcal{T}(1)$ the Velling-Kirillov metric is given by

$$
\langle \partial_ {z}, \partial_ {z} \rangle_ {V K} (0, z) = \frac {1}{(1 - | z | ^ {2}) ^ {2}},
$$

$$
\langle \partial_ {z}, \tau_ {\mu} \rangle_ {V K} (0, z) = 0,
$$

$$
\left\langle \tau_ {\mu}, \tau_ {\mu} \right\rangle_ {V K} (0, z) = \frac {1}{2} \iint_ {\mathbb {D} ^ {*}} G (z, u) | \mu (u) | ^ {2} \rho (u) d ^ {2} u.
$$

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

(ii) On the fiber $\pi^{-1}(0)\subset \mathcal{T}(1)$ the (1,1)-form $\Theta$ is given by

$$
\Theta \left(\partial_ {z}, \partial_ {\bar {z}}\right) (0, z) = - \frac {2}{(1 - | z | ^ {2}) ^ {2}},
$$

$$
\Theta \left(\partial_ {z}, \tau_ {\bar {\mu}}\right) (0, z) = 0,
$$

$$
\Theta \left(\tau_ {\mu}, \tau_ {\bar {\mu}}\right) (0, z) = - \iint_ {\mathbb {D} ^ {*}} G (z, u) | \mu (u) | ^ {2} \rho (u) d ^ {2} u.
$$

<!-- page 51 of 136 -->

42

1. CURVATURE PROPERTIES AND CHERN FORMS

(iii) The vertical holomorphic tangent bundle $V \to \mathcal{T}(1)$ of the fibration $\pi : \mathcal{T}(1) \to T(1)$ is a negative line bundle.

PROOF. It follows from the property TV2 in Section 1.2.2 that the vector field $\partial_z$ at $(0,z)\in \pi^{-1}(0)$ corresponds to the tangent vector

$$
\mathrm{u} = \sum_ {n \in \mathbb {Z} \backslash \{0 \}} c _ {n} e ^ {i n \theta} \frac {d}{d \theta} \in T _ {0} ^ {\mathbb {R}} S ^ {1} \backslash \operatorname{Homeo} _ {q s} \left(S ^ {1}\right)
$$

with $c_{1} = \frac{1 - \bar{z}}{(1 - z)(1 - |z|^{2})}$ and $c_{n} = 0$ for $n \geq 2$. This proves the first formula in part (i). The second formula follows from the fact that, according to the property TS1 in Section 1.2.3, the tangent vector $u \in T_0^{\mathbb{R}}S^1 \backslash \mathrm{Homeo}_{qs}(S^1)$ which corresponds to the horizontal lift $\tau_{\mu}$ of the vector field $\frac{\partial}{\partial\varepsilon_{\mu}}$ to $(0,z) \in \pi^{-1}(0)$, has $c_{1} = 0$. The last formula follows from the following lemma.

LEMMA 5.8. Let $\mu \in \Omega^{-1,1}(\mathbb{D}^*)$ and

$$
\phi (z) = D _ {0} \beta (\mu) (z) = \sum_ {n = 2} ^ {\infty} (n ^ {3} - n) a _ {n} z ^ {n - 2} \in A _ {\infty} (\mathbb {D}).
$$

Then

$$
\iint_ {\mathbb {D} ^ {*}} G (z, u) | \mu (u) | ^ {2} \rho (u) d ^ {2} u = 2 \sum_ {n = 2} ^ {\infty} n | a _ {n} ^ {z} | ^ {2},
$$

where

$$
(\sigma_ {z} ^ {- 1}) ^ {*} (\phi) (u) = \sum_ {n = 2} ^ {\infty} (n ^ {3} - n) a _ {n} ^ {z} u ^ {n - 2}
$$

is the power series expansion of $(\sigma_z^{-1})^*(\phi) = \phi \circ \sigma_z^{-1}\left((\sigma_z^{-1})'\right)^2 \in A_\infty(\mathbb{D})$.

PROOF. Since $G(z,u)$ is a point-pair invariant, it is sufficient to prove the formula for $z = \infty$. In this case, using the relation $G(\infty ,u) = G(0,1 / \bar{u})$ between the resolvent kernels on $\mathbb{D}^*$ and $\mathbb{D}$ and the formula $\mu = \Lambda (\phi)$ we get

$$
\iint_ {\mathbb {D} ^ {*}} G (\infty , u) | \mu (u) | ^ {2} \rho (u) d ^ {2} u = \iint_ {\mathbb {D}} G (0, u) (1 - | u | ^ {2}) ^ {2} | \phi (u) | ^ {2} d ^ {2} u.
$$

It follows from the explicit formula (1.19) that

$$
(1 - | u | ^ {2}) ^ {2} G (0, u) = h (r) = \left(\frac {1}{2 \pi} \frac {1 + r ^ {2}}{1 - r ^ {2}} \log \frac {1}{r ^ {2}} - \frac {1}{\pi}\right) (1 - r ^ {2}) ^ {2}, r = | u |.
$$

Since $h$ is an integrable function on $[0,1)$, we have

$$
\iint_ {\mathbb {D}} G (0, u) (1 - | u | ^ {2}) ^ {2} | \phi (u) | ^ {2} d ^ {2} u = 2 \pi \sum_ {n = 2} ^ {\infty} (n ^ {3} - n) ^ {2} | a _ {n} | ^ {2} \int_ {0} ^ {1} h (r) r ^ {2 n - 4} r d r.
$$

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

A straightforward computation gives

$$
\int_ {0} ^ {1} h (r) r ^ {2 n - 4} r d r = \frac {1}{\pi} \frac {1}{(n ^ {3} - n) (n ^ {2} - 1)},
$$

which proves the lemma.

<!-- page 52 of 136 -->

5. CHARACTERISTIC FORMS OF THE UNIVERSAL TEICHMÜLLER CURVE

43

Using this Lemma, the property TV1 in Section 1.2.2 and the property TS2 in Section 1.2.3, we get the third formula in part (i). Now part (ii) follows from Theorem 5.3, and part (iii) follows from part (ii) and the property RK2 in Section 1.4.

REMARK 5.9. Parts (ii) and (iii) of Proposition 5.7 generalize Wolpert's computation of the $(1,1)$-form $\Theta$ for finite-dimensional Teichmüller spaces (see Theorem 5.5 and formula (5.3) in [Wol86]).

5.3. Mumford-Morita-Miller characteristic forms. In this section we consider $\pi : \mathcal{T}(1) \to T(1)$ as a holomorphic fibration of Hilbert manifolds and evaluate the Mumford-Morita-Miller forms $\kappa_n$ on $T(1)$.

THEOREM 5.10. The characteristic forms $\kappa_{n}$ are right-invariant on the Hilbert manifold $T(1)$ and for $\mu_1,\ldots ,\mu_n,\nu_1,\dots ,\nu_n\in H^{-1,1}(\mathbb{D}^*)\simeq T_0T(1)$

$$
\begin{array}{c} \kappa_ {n} (\mu_ {1}, \dots , \mu_ {n}, \bar {\nu} _ {1}, \dots , \bar {\nu} _ {n}) \\ = \frac {i ^ {n} (n + 1) !}{(2 \pi) ^ {n + 1}} \sum_ {\sigma \in S _ {n}} s g n (\sigma) \iint_ {\mathbb {D} ^ {*}} G (\mu_ {1} \bar {\nu} _ {\sigma (1)}) \dots G (\mu_ {n} \bar {\nu} _ {\sigma (n)}) \rho (z) d ^ {2} z, \end{array}
$$

where the sum goes over the permutation group $S_{n}$ on $n$ elements and $\text{sgn}(\sigma)$ is the sign of the permutation $\sigma$.

PROOF. It is straightforward computation of the integral

$$
\begin{array}{c} \kappa_ {n} (\mu_ {1}, \dots , \mu_ {n}, \bar {\nu} _ {1}, \dots , \bar {\nu} _ {n}) \\ = \left(\frac {- i}{2 \pi}\right) ^ {n + 1} \iint_ {\mathbb {D} ^ {*}} \Theta^ {n + 1} \left(\partial_ {z}, \partial_ {\bar {z}}, \tau_ {\mu_ {1}}, \tau_ {\bar {\nu} _ {1}}, \dots , \tau_ {\mu_ {n}}, \tau_ {\bar {\nu} _ {n}}\right) d z \wedge d \bar {z} \end{array}
$$

using Part (ii) of Proposition 5.7. We need only to verify that the integral is convergent. This follows from the properties of the resolvent kernel in Section 1.4. Indeed, the property RK3 assures that $G(\mu \bar{\nu})$ is bounded on $\mathbb{D}^*$ for $\mu, \nu \in \Omega^{-1,1}(\mathbb{D}^*)$, and properties RK2 and RK4 imply that for $\mu, \nu \in H^{-1,1}(\mathbb{D}^*)$,

$$
\begin{array}{l} \left| \iint_ {\mathbb {D} ^ {*}} G (\mu \bar {\nu}) \rho (z) d ^ {2} z \right| \leq \iint_ {\mathbb {D} ^ {*}} \iint_ {\mathbb {D} ^ {*}} G (z, u) | \mu (u) \nu (u) | \rho (u) \rho (z) d ^ {2} u d ^ {2} z \\ \qquad = \iint_ {\mathbb {D} ^ {*}} \iint_ {\mathbb {D} ^ {*}} G (z, u) | \mu (u) \nu (u) | \rho (z) \rho (u) d ^ {2} z d ^ {2} u \\ \qquad = \iint_ {\mathbb {D} ^ {*}} | \mu (u) \nu (u) | \rho (u) d ^ {2} u <   \infty . \end{array}
$$

COROLLARY 5.11. On the Hilbert manifold $T(1)$

$$
\kappa_ {1} = \frac {1}{\pi^ {2}} \omega_ {W P}.
$$

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

<!-- page 53 of 136 -->

44

1. CURVATURE PROPERTIES AND CHERN FORMS

PROOF. We have, using again the property RK4 in Section 1.4,

$$
\begin{array}{c} \hline \kappa_ {1} (\mu , \bar {\nu}) = \frac {i}{2 \pi^ {2}} \iint_ {\mathbb {D} ^ {*}} G (\mu \bar {\nu}) \rho (z) d ^ {2} z = \frac {i}{2 \pi^ {2}} \iint_ {\mathbb {D} ^ {*}} \mu (z) \overline {{\nu (z)}} \rho (z) d ^ {2} z \\ = \frac {1}{\pi^ {2}} \omega_ {W P} (\mu , \bar {\nu}). \end{array}
$$

REMARK 5.12. Combining Corollary 5.11, Part (ii) of Proposition 5.7 and Theorem 5.3, we get another proof of Theorem 4.3 in [Teo04].

REMARK 5.13. Theorem 5.10 generalizes Wolpert's result for finite-dimensional Teichmüller spaces (see Lemma 5.9 and Lemma 5.10 in [Wol86]) to the universal Teichmüller space.

## 6. First and second variations of the hyperbolic metric

Here we present a concise formula for the second variation of the hyperbolic metric in terms of the resolvent kernel. We are using the model $\mathbb{H}^2\simeq \mathbb{U}$, so that the density of the hyperbolic metric is the $(1,1)$ - tensor $\rho (z) = y^{-2}$ on $\mathbb{U}$.

6.1. The first variation. It is a classical result of Ahlfors [Ahl61] that the first variation of the hyperbolic metric at the origin of $T(1)$ is identically zero.

LEMMA 6.1. For every $\mu \in \Omega^{-1,1}(\mathbb{U})$,

$$
L _ {\mu} \rho = 0.
$$

PROOF. Since

$$
\rho^ {\varepsilon \mu} = w _ {\varepsilon \mu} ^ {*} (\rho) = - \frac {4 \left| (w _ {\varepsilon \mu}) _ {z} (z) \right| ^ {2}}{(w _ {\varepsilon \mu} (z) - \overline {{w _ {\varepsilon \mu} (z)}}) ^ {2}},
$$

we have

$$
L _ {\mu} \rho (z) = \frac {\partial}{\partial \varepsilon} \Big | _ {\varepsilon = 0} \rho^ {\varepsilon \mu} (z) = - 4 \frac {F _ {z} (z) + \overline {{\Phi^ {\prime} (z)}}}{(z - \bar {z}) ^ {2}} + 8 \frac {F (z) - \overline {{\Phi (z)}}}{(z - \bar {z}) ^ {3}},
$$

where $F = F[\mu], \Phi = \Phi[\mu]$, and the result follows from Lemma 1.13.

REMARK 6.2. For the case $\mu \in \Omega^{-1,1}(\mathbb{U},\Gamma)$, where $\Gamma$ is a cofinite Fuchsian group, another proof of the Ahlfors result was given by Wolpert [Wol86].

6.2. The second variation. Set

$$
L _ {\mu} L _ {\bar {\mu}} \rho = \left. \frac {\partial^ {2}}{\partial \varepsilon \partial \bar {\varepsilon}} \right| _ {\varepsilon = 0} \rho^ {\varepsilon \mu}.
$$

We have

PROPOSITION 6.3. For every $\mu \in \Omega^{-1,1}(\mathbb{U})$,

$$
L _ {\mu} L _ {\widetilde {\mu}} \rho = \rho G (| \mu | ^ {2}).
$$

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

<!-- page 54 of 136 -->

6. FIRST AND SECOND VARIATIONS OF THE HYPERBOLIC METRIC

45

PROOF. Using the representation

$$
\rho^ {\varepsilon \mu} (z) = - 4 K _ {\varepsilon \mu} (z, \bar {z})\tag{6.1}
$$

and the first formula in (1.25) we get


> **[IMPLICIT HYPOTHESIS W1-12]** (2605–2610; Lean: `eq_6_2` (S6Eq62), `eq_1_25` (Eq124General; via eq_6_2)) H: "small" is made precise as ‖εμ‖∞ < 1, so that w_{εμ} exists. F: the PV is explicit (round discs in the source plane; 下属3 checked that the excision shape does not matter, LEADER 2026-10-27).

$$
\frac {\partial}{\partial \varepsilon} \rho^ {\varepsilon \mu} (z) = \frac {4}{\pi} \iint_ {\mathbb {U}} \mu (u) K _ {\varepsilon \mu} (z, u) K _ {\varepsilon \mu} (u, \bar {z}) d ^ {2} u,\tag{6.2}
$$

where the integral is understood in the principal value sense. Setting $\varepsilon = 0$ in (6.2) and using Lemma 6.1, we obtain

$$
\iint_ {\mathbb {U}} \frac {\mu (u)}{(u - z) ^ {2} (u - \bar {z}) ^ {2}} d ^ {2} u = 0 \text {for all} z \in \mathbb {U}.\tag{6.3}
$$

Using formulas (1.24) and (1.25), we get from (6.2) the following integral representation for the second variation of the hyperbolic metric

$$
\begin{array}{c} L _ {\mu} L _ {\bar {\mu}} \rho (z) = - \frac {4}{\pi^ {2}} \iint_ {\mathbb {U}} \iint_ {\mathbb {U}} \mu (u) \overline {{\mu (v)}} \left(\frac {1}{(u - \bar {v}) ^ {2} (z - \bar {v}) ^ {2} (u - \bar {z}) ^ {2}} \right. \\ \qquad \qquad \qquad + \left. \frac {1}{(u - z) ^ {2} (u - \bar {v}) ^ {2} (\bar {z} - \bar {v}) ^ {2}}\right) d ^ {2} u d ^ {2} v. \end{array}\tag{6.4}
$$

The differentiation under the integral sign is justified by the same argument as in [Ahl62]. We transform the principal value integrals in (6.4) into the ordinary integrals by using the identity

$$
\frac {1}{u - \bar {v}} = \frac {z - \bar {z}}{(u - \bar {z}) (z - \bar {v})} + \frac {(\bar {v} - \bar {z}) (z - u)}{(u - \bar {z}) (z - \bar {v}) (u - \bar {v})},\tag{6.5}
$$

which gives

$$
\begin{array}{r l} & {\frac {1}{(u - z) ^ {2} (u - \bar {v}) ^ {2} (\bar {z} - \bar {v}) ^ {2}}} \\ & {= \frac {1}{(u - \bar {z}) ^ {2} (z - \bar {v}) ^ {2} (u - \bar {v}) ^ {2}} + \frac {2 (z - \bar {z})}{(u - \bar {z}) ^ {3} (z - \bar {v}) ^ {3} (u - \bar {v})}} \\ & {+ \frac {(z - \bar {z}) ^ {2}}{(u - z) ^ {2} (u - \bar {z}) ^ {2} (z - \bar {v}) ^ {2} (\bar {z} - \bar {v}) ^ {2}} + \frac {2 (z - \bar {z}) ^ {2}}{(u - z) (u - \bar {z}) ^ {3} (z - \bar {v}) ^ {3} (\bar {z} - \bar {v})}.} \end{array}
$$

Using (6.3) and Corollary 1.15 we see that last two terms in this formula do not contribute into the representation (6.4) and we obtain

$$
\begin{array}{l} L _ {\mu} L _ {\bar {\mu}} \rho (z) = - \frac {8}{\pi^ {2}} \iint_ {\mathbb {U}} \iint_ {\mathbb {U}} \mu (u) \overline {{\mu (v)}} \left(\frac {1}{(u - \bar {v}) ^ {2} (z - \bar {v}) ^ {2} (u - \bar {z}) ^ {2}} \right. \\ \qquad \qquad \qquad + \left. \frac {(z - \bar {z})}{(u - \bar {z}) ^ {3} (u - \bar {v}) (z - \bar {v}) ^ {3}}\right) d ^ {2} u d ^ {2} v. \end{array}
$$

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

<!-- page 55 of 136 -->

46

1. CURVATURE PROPERTIES AND CHERN FORMS

Now we apply the operator $2(\Delta_0 + \frac{1}{2})$ to the bounded function $\rho^{-1}L_{\mu}L_{\bar{\mu}}\rho$ on $\mathbb{U}$. Using (6.5) it is straightforward to compute that

$$
\begin{array}{c} (2 \Delta_ {0} + 1) \left(\frac {(z - \bar {z}) ^ {2}}{(u - \bar {v}) ^ {2} (z - \bar {v}) ^ {2} (u - \bar {z}) ^ {2}} + \frac {(z - \bar {z}) ^ {3}}{(u - \bar {z}) ^ {3} (u - \bar {v}) (z - \bar {v}) ^ {3}}\right) \\ = \frac {9}{2} \frac {(z - \bar {z}) ^ {4}}{(u - \bar {z}) ^ {4} (z - \bar {v}) ^ {4}}, \end{array}
$$

which, together with (1.23), gives

$$
\begin{array}{c} (2 \Delta_ {0} + 1) \left(\rho^ {- 1} L _ {\mu} L _ {\bar {\mu}} \rho\right) (z) \\ = \frac {9}{\pi^ {2}} \iint_ {\mathbb {U}} \iint_ {\mathbb {U}} \mu (u) \overline {{\mu (v)}} \frac {(z - \bar {z}) ^ {4}}{(u - \bar {z}) ^ {4} (z - \bar {v}) ^ {4}} d ^ {2} u d ^ {2} v = | \mu (z) | ^ {2}. \end{array}
$$

Using the property RK3 in Section 1.4 completes the proof.

COROLLARY 6.4. For every $\mu, \nu \in \Omega^{-1,1}(\mathbb{D}^*)$,


> **[ERRATUM W1-01]** (2662–2666; Lean: `cor_6_4` (S6_HyperbolicMetricVariation)) Domain misprint: the formula is the 𝕌-model one (kernels with u − v̄, z − z̄). The correct statement reads Ω^{-1,1}(𝕌).

$$
\begin{array}{c} G (\mu \bar {\nu}) (z) = \frac {2}{\pi^ {2}} \iint_ {\mathbb {U}} \iint_ {\mathbb {U}} \mu (u) \overline {{\nu (v)}} \left(\frac {(z - \bar {z}) ^ {2}}{(u - \bar {v}) ^ {2} (z - \bar {v}) ^ {2} (u - \bar {z}) ^ {2}} \right. \\ \qquad + \left. \frac {(z - \bar {z}) ^ {3}}{(u - \bar {z}) ^ {3} (u - \bar {v}) (z - \bar {v}) ^ {3}}\right) d ^ {2} u d ^ {2} v. \end{array}
$$

REMARK 6.5. It follows from Proposition 6.3 by polarization that

$$
L _ {\mu} L _ {\bar {\nu}} \rho = \left. \frac {\partial^ {2}}{\partial \varepsilon_ {1} \partial \bar {\varepsilon} _ {2}} \right| _ {\varepsilon_ {1} = \varepsilon_ {2} = 0} \rho^ {\varepsilon_ {1} \mu + \varepsilon_ {2} \nu} = \rho G (\mu \bar {\nu}).
$$

REMARK 6.6. For the case $\mu \in \Omega^{-1,1}(\mathbb{U},\Gamma)$, where $\Gamma$ is a cofinite Fuchsian group, the formula for the second variation of the hyperbolic metric in Proposition 6.3 was first proved by Wolpert [Wol86]. However, the method in [Wol86] does not work for the universal Teichmüller space $T(1)$. The proof of Proposition 6.3 shows that the original singular integral representation (6.4) of Ahlfors can be easily transformed to a closed form using the resolvent kernel.

## 7. Riemann curvature tensor

In this section we consider $T(1)$ as a Hilbert manifold equipped with the Weil-Petersson metric. We prove that the Weil-Petersson metric is Kähler, compute its Riemann and Ricci tensors, and show that the Ricci, holomorphic, and sectional curvatures are all negative. Since the Weil-Petersson metric is right-invariant, it is sufficient to compute these tensors at the origin of $T(1)$.

7.1. The first variation of the Weil-Petersson metric. For the case $\mu, \nu \in \Omega^{-1,1}(\mathbb{D}^*)$ set

$$
Q (\mu , \nu) = P (R (\mu , \nu)) \circ w _ {\nu} \frac {(\overline {{w _ {\nu}}}) _ {\bar {z}}}{(w _ {\nu}) _ {z}}.
$$

PROPOSITION 7.1. For $\mu, \nu \in \Omega^{-1,1}(\mathbb{D}^*)$,

$$
\begin{array}{l} \frac {\partial}{\partial \varepsilon} Q (\mu , \varepsilon \nu) \Big | _ {\varepsilon = 0} = 0, \\ \frac {\partial}{\partial \bar {\varepsilon}} Q (\mu , \varepsilon \nu) \Big | _ {\varepsilon = 0} = - 2 \frac {\partial}{\partial \bar {z}} \rho^ {- 1} \frac {\partial}{\partial \bar {z}} G (\mu \bar {\nu}). \end{array}
$$

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

<!-- page 56 of 136 -->

7. RIEMANN CURVATURE TENSOR

47

PROOF. We use complex anti-linear isomorphism $\Omega^{-1,1}(\mathbb{D}^*)\simeq \Omega^{-1,1}(\mathbb{D})$, given by the reflection (1.1), and the model $\mathbb{H}^2\simeq \mathbb{U}$ of the hyperbolic plane. From (1.6) we get

$$
\rho^ {\varepsilon \nu} (z) Q (\mu , \varepsilon \nu) (z) = \frac {1 2}{\pi} \iint_ {\mathbb {U}} \mu (u) K _ {\varepsilon \nu} (u, \bar {z}) ^ {2} d ^ {2} u.\tag{7.1}
$$

It follows from equations (1.25) that

$$
\left. \frac {\partial}{\partial \varepsilon} \right| _ {\varepsilon = 0} Q (\mu , \varepsilon \nu) (z) = \frac {6 (z - \bar {z}) ^ {2}}{\pi^ {2}} \iint_ {\mathbb {U}} \iint_ {\mathbb {U}} \frac {\mu (u) \nu (v)}{(u - \bar {z}) ^ {2} (u - v) ^ {2} (v - \bar {z}) ^ {2}} d ^ {2} u d ^ {2} v\tag{7.2}
$$

and

$$
\left. \frac {\partial}{\partial \bar {\varepsilon}} \right| _ {\varepsilon = 0} Q (\mu , \varepsilon \nu) (z) = \frac {6 (z - \bar {z}) ^ {2}}{\pi^ {2}} \iint_ {\mathbb {U}} \iint_ {\mathbb {U}} \frac {\mu (u) \overline {{\nu (v)}}}{(u - \bar {z}) ^ {2} (u - \bar {v}) ^ {2} (\bar {v} - \bar {z}) ^ {2}} d ^ {2} u d ^ {2} v.\tag{7.3}
$$

The integrals are understood in the principal value sense and differentiation under the integral sign in (7.1) is justified as in [Ahl62].

To prove that the integral (7.2) is zero, we use the identity

$$
\frac {1}{(u - v) (u - \bar {z}) (v - \bar {z})} = \frac {1}{(u - v) ^ {2}} \left(\frac {1}{v - \bar {z}} - \frac {1}{u - \bar {z}}\right),
$$

and rewrite the integral (7.2) as follows

$$
\left| \begin{array}{c}\iintop_{\mathbb{U}}\iintop_{\mathbb{U}}\frac{\mu(u)\nu(v)}{(u - \bar{z})^{2}(u - v)^{2}(v - \bar{z})^{2}} d^{2}ud^{2}v\\ = \lim_{\varepsilon \to 0}\iiintop_{\mathbb{U}\times \mathbb{U}\setminus \{|u - v| <   \varepsilon \}}\left(\frac{1}{(u - v)^{4}(v - \bar{z})^{2}} -\frac{2}{(u - v)^{5}(v - \bar{z})} \right.\\ +\left.\frac{2}{(u - v)^{5}(u - \bar{z})} +\frac{1}{(u - v)^{4}(u - \bar{z})^{2}}\right)\mu (u)\nu (v)d^{2}ud^{2}v\\ = I_{1} + I_{2} + I_{3} + I_{4}. \end{array} \right|\tag{7.4}
$$


> **[ERRATUM W1-02]** (2729–2732; Lean: `eq_7_4` (S7Eq74)) Misprint in the variable assignment: I₁ and I₂ are principal values over u, while I₃ and I₄ are over v (after the change of order). Found by 下属6.
> **[IMPLICIT HYPOTHESIS W1-03]** (2729–2740; Lean: `eq_7_4` (S7Eq74)) For bounded harmonic data (no decay at ∞) a single I_k is not absolutely integrable: log divergence at ∞, and a strip near ℝ (下属6, EQ74 triage). The memoir tacitly reads each term as an iterated, conditionally convergent integral.

Applying Lemma (1.12) to the principal value integrals over $u$ in the terms $I_1, I_2$ and $I_4$, we conclude that these terms vanish. Changing the order of integrations in $I_3$ (which is legitimate since domain of integration is invariant under the involution $(u,v)\mapsto (v,u)$) and applying Lemma (1.12) to the integral over $v$ we conclude that the term $I_3$ also vanishes. This proves that the holomorphic variation of $Q(\mu ,\nu)$ vanishes.

To prove the formula for the antiholomorphic variation, we again use the identity (6.5), which gives

$$
\begin{array}{r l} & {\left| \frac {1}{(u - \bar {z}) ^ {2} (u - \bar {v}) ^ {2} (\bar {v} - \bar {z}) ^ {2}} = \frac {(u - z) ^ {2}}{(u - \bar {z}) ^ {4} (\bar {v} - z) ^ {2} (u - \bar {v}) ^ {2}} \right.} \\ & {\left. + \frac {(z - \bar {z}) ^ {2}}{(u - \bar {z}) ^ {4} (\bar {v} - \bar {z}) ^ {2} (\bar {v} - z) ^ {2}} + \frac {2 (z - \bar {z}) ^ {2} (z - u)}{(u - \bar {z}) ^ {5} (z - \bar {v}) ^ {3} (\bar {v} - \bar {z})} \right.} \\ & {\left. + \frac {2 (z - \bar {z}) (z - u) ^ {2}}{(u - \bar {z}) ^ {5} (z - \bar {v}) ^ {3} (u - \bar {v})}. \right.} \end{array}
$$

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

<!-- page 57 of 136 -->

48

1. CURVATURE PROPERTIES AND CHERN FORMS

Using formula (6.3) and Corollary 1.15 we see that the second and third terms do not contribute to (7.3), and we get

$$
\begin{array}{l} \frac {\partial}{\partial \bar {\varepsilon}} \bigg | _ {\varepsilon = 0} Q (\mu , \varepsilon \nu) (z) = \frac {6 (z - \bar {z}) ^ {2}}{\pi^ {2}} \iint_ {\mathbb {U}} \iint_ {\mathbb {U}} \mu (u) \overline {{\nu (v)}} \\ \left(\frac {(u - z) ^ {2}}{(u - \bar {z}) ^ {4} (\bar {v} - z) ^ {2} (u - \bar {v}) ^ {2}} + \frac {2 (z - \bar {z}) (z - u) ^ {2}}{(u - \bar {z}) ^ {5} (z - \bar {v}) ^ {3} (u - \bar {v})}\right) d ^ {2} u ^ {2} v. \end{array}\tag{7.5}
$$

Now applying  $\partial_{\bar{z}}\rho^{-1}\partial_{\bar{z}}$  to the integral representation in Corollary 6.4 (the differentiation under the integral sign being trivially justified) we get the formula for the antiholomorphic variation.

Set

$$
\dot {Q} (\mu) [ \nu ] = \left. \frac {\partial}{\partial \bar {\varepsilon}} \right| _ {\varepsilon = 0} Q (\mu , \varepsilon \nu).
$$

PROPOSITION 7.2. Let $\mu \in H^{-1,1}(\mathbb{D}^*)$ and $\nu \in \Omega^{-1,1}(\mathbb{D}^*)$. Then $\dot{Q} (\mu)[\nu] \in L^{2}(\mathbb{D}^{*},\rho (z)d^{2}z)$ and

$$
\left\| \dot {Q} (\mu) [ \nu ] \right\| _ {2} ^ {2} = \| \mu \bar {\nu} \| _ {2} ^ {2} - (\mu \bar {\nu}, G (\mu \bar {\nu})),
$$

where ( , ) stands for the inner product in the Hilbert space $L^2(\mathbb{D}^*, \rho(z)d^2z)$.

PROOF. As in the proof of Proposition 7.1, it is convenient to use the isomorphism $\Omega^{-1,1}(\mathbb{D}^*) \simeq \Omega^{-1,1}(\mathbb{D})$. For $\mu \in BC^{\infty}(\mathbb{D}) \cap L^{2}(\mathbb{D}, \rho(z)d^{2}z)$ with compact support and $\nu \in BC^{\infty}(\mathbb{D})$ we set

$$
\mathcal {Q} _ {\nu} (\mu) = 2 \frac {\partial}{\partial \bar {z}} \rho^ {- 1} \frac {\partial}{\partial \bar {z}} G (\mu \bar {\nu}).
$$

We will prove that $\| \mathcal{Q}_{\nu}(\mu)\|_{2}^{2} = \| \mu \bar{\nu}\|_{2}^{2} - (\mu \bar{\nu},G(\mu \bar{\nu}))$, so that $\mathcal{Q}_{\nu}$ extends to a bounded linear operator on $L^2 (\mathbb{D},\rho (z)d^2 z)$. Since, according to Proposition 7.1, $\mathcal{Q}_{\nu}(\mu) = -\dot{Q} (\mu)[\nu ]$ for $\mu \in H^{-1,1}(\mathbb{D}^{*})$ and $\nu \in \Omega^{-1,1}(\mathbb{D}^{*})$, the assertion follows from this fact.

From the explicit formula (1.19) we get the following estimates

$$
\begin{array}{c} G (z, w) = O ((1 - | z | ^ {2})), \quad (\partial_ {z} \rho^ {- 1} \partial_ {z}) G (z, w) = O ((1 - | z | ^ {2})), \\ \partial_ {z} G (z, w) = O (1), \quad \left(\partial_ {\bar {z}} \left(\partial_ {z} \rho^ {- 1} \partial_ {z}\right)\right) G (z, w) = O (1) \quad \text {as} \quad | z | \to 1, \end{array}\tag{7.6}
$$

uniformly as $w$ varies on compact subsets of $\mathbb{D}$. Using Stokes' theorem and the identity

$$
\rho^ {- 1} \partial_ {z} \rho^ {- 1} \partial_ {z} \rho \partial_ {\bar {z}} \rho^ {- 1} \partial_ {\bar {z}} = \Delta_ {0} (\Delta_ {0} + \frac {1}{2})
$$

we get

$$
\begin{array}{l} \iint_ {\mathbb {D}} | \mathcal {Q} _ {\nu} (\mu) | ^ {2}   \rho (z) d ^ {2} z = 4 \iint_ {\mathbb {D}} \partial_ {z} \left(\rho^ {- 1} \partial_ {z} G (\bar {\mu} \nu)\right) \partial_ {\bar {z}} \left(\rho^ {- 1} \partial_ {\bar {z}} G (\mu \bar {\nu})\right) \rho (z) d ^ {2} z \\ \qquad = 4 \iint_ {\mathbb {D}} \Delta_ {0} (\Delta_ {0} + \frac {1}{2}) G (\mu \bar {\nu}) G (\bar {\mu} \nu) \rho (z) d ^ {2} z \\ \qquad = 2 \iint_ {\mathbb {D}} \Delta_ {0} (\mu \bar {\nu}) G (\bar {\mu} \nu) \rho (z) d ^ {2} z, \end{array}
$$

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

<!-- page 58 of 136 -->

7. RIEMANN CURVATURE TENSOR

49

where in the last line we have used property RK3 from Section 1.4. Due to the estimates (7.6) the boundary terms arising in the Stokes' formula vanish. Using Stokes' theorem once again we finally get

$$
\begin{array}{l} \iint_ {\mathbb {D}} | \mathcal {Q} _ {\nu} (\mu) | ^ {2} \rho (z) d ^ {2} z = 2 \iint_ {\mathbb {D}} \mu \bar {\nu} \Delta_ {0} G (\bar {\mu} \nu) \rho (z) d ^ {2} z \\ \qquad \qquad \qquad = \iint_ {\mathbb {D}} | \mu \bar {\nu} | ^ {2} \rho (z) d ^ {2} z - \iint_ {\mathbb {D}} \mu \bar {\nu} G (\bar {\mu} \nu) \rho (z) d ^ {2} z \\ \qquad \qquad \qquad = \| \mu \bar {\nu} \| _ {2} ^ {2} - (\mu \bar {\nu}, G (\mu \bar {\nu})). \end{array}
$$

The boundary terms again vanish due to (7.6) and Remark 3.2.

COROLLARY 7.3. For $\mu, \nu \in H^{-1,1}(\mathbb{D}^*)$ and $\kappa \in \Omega^{-1,1}(\mathbb{D}^*)$,

$$
\left(\dot {Q} (\mu) [ \kappa ], \dot {Q} (\nu) [ \kappa ]\right) = (\mu \bar {\kappa}, \nu \bar {\kappa}) - (\mu \bar {\kappa}, G (\nu \bar {\kappa})).
$$

THEOREM 7.4. For $\mu, \nu \in H^{-1,1}(\mathbb{D}^*)$ and $\kappa \in \Omega^{-1,1}(\mathbb{D}^*)$,

$$
\left. \frac {\partial}{\partial \varepsilon} g _ {\mu \bar {\nu}} (\varepsilon \kappa) \right| _ {\varepsilon = 0} = 0.
$$

PROOF. Since $P^2 = P$, we get from (4.3),


> **[ERRATUM W1-06]** (2824–2838; Lean: proof of `thm_7_4` (S7_Curvature)) Two problems with the proof as printed; the theorem itself is true. (i) The first term should be (∂_ε Q(μ,εκ)\|₀, ν), which is 0 by Prop. 7.1(i), not (Q̇(μ)[κ], ν), where Q̇ = ∂_ε̄. (ii) The displayed lines give ∂_ε g = (μ, Q̇(ν)[κ]) from both forms of (7.7), but do not show that this vanishes. The missing step is Wolpert's: by Prop. 7.1, Q̇(ν)[κ] = −2∂_z̄(ρ⁻¹∂_z̄ G(νκ̄)) is ∂̄-exact, hence orthogonal to H^{-1,1} after integration by parts. Confidence: high on (i), medium on (ii).

$$
g _ {\mu \bar {\nu}} (\kappa) = \iint_ {\mathbb {D} ^ {*}} Q (\mu , \kappa) \overline {{Q (\nu , \kappa)}} (1 - | \kappa | ^ {2}) w _ {\kappa} ^ {*} (\rho) (z) d ^ {2} z = \iint_ {\mathbb {D} ^ {*}} \mu \overline {{Q (\nu , \kappa)}} w _ {\kappa} ^ {*} (\rho) (z) d ^ {2} z,\tag{7.7}
$$

so that

$$
\left. \frac {\partial}{\partial \varepsilon} g _ {\mu \overline {{\nu}}} (\varepsilon \kappa) \right| _ {\varepsilon = 0} = \left(\dot {Q} (\mu) [ \kappa ], \nu\right) + \left(\mu , \dot {Q} (\nu) [ \kappa ]\right) = \left(\mu , \dot {Q} (\nu) [ \kappa ]\right).
$$

Differentiation under the integral sign is justified as in [Ahl62]. Thus for all $\mu, \nu \in H^{-1,1}(\mathbb{D}^*)$ and $\kappa \in \Omega^{-1,1}(\mathbb{D}^*)$

$$
\left(\dot {Q} (\mu) [ \kappa ], \nu\right) = 0,
$$

and the theorem follows.

Let $\{\mu_n\}_{n=2}^{\infty}$ be an orthonormal basis for the Hilbert space $H^{-1,1}(\mathbb{D}^{*})$,

$$
\mu_ {n} (z) = - \sqrt {\frac {n ^ {3} - n}{8 \pi}} (1 - | z | ^ {2}) ^ {2} \bar {z} ^ {- n - 2}, n = 2, 3, \dots ,
$$

and let $\{\varepsilon_n\}_{n=2}^{\infty}$ be the corresponding Bers coordinates on the chart $V_0$. Since $\|\mu\|_2 = 2\|D_0\beta(\mu)\|_2$, it follows from Section 2.3 that $\sum_{n=2}^{\infty} |\varepsilon_n|^2 < \frac{4\pi}{3}$. Denote by $\frac{\partial}{\partial\varepsilon_n}$ the corresponding directional derivatives — the vector field $\frac{\partial}{\partial\varepsilon_{\mu_n}}$ on $V_0$, and set $g_{m\bar{n}} = g_{\mu_m\bar{\mu}_n}$. Since the basis $\{\mu_n\}_{n=2}^{\infty}$ is orthonormal, $g_{m\bar{n}} = \delta_{mn}$ at the origin of $T(1)$.

COROLLARY 7.5. The Weil-Petersson metric is a Kähler metric on the Hilbert manifold $T(1)$, and the Bers coordinates are geodesic coordinates at the origin of $T(1)$.

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

<!-- page 59 of 136 -->

50

1. CURVATURE PROPERTIES AND CHERN FORMS

PROOF. It follows from Theorem 7.4 that

$$
\frac {\partial g _ {m \bar {n}}}{\partial \varepsilon_ {l}} (0) = 0.
$$

REMARK 7.6. Propositions 7.1 and 7.2 and Theorem 7.4 generalize Wolpert's results for finite-dimensional Teichmüller spaces (see Lemma 2.7 and Theorem 2.9 in [Wol86]) to the universal Teichmüller space. In particular, our proof of Theorem 7.4 (after Proposition 7.2 has been established) is the same as in [Wol86].

7.2. The second variation of the Weil-Petersson metric. Due to Corollary 7.5, the Riemann tensor of the Weil-Petersson metric at the origin of $T(1)$ is given by

$$
R _ {k \bar {l} m \bar {n}} = - \frac {\partial^ {2} g _ {k \bar {l}}}{\partial \varepsilon_ {m} \partial \bar {\varepsilon} _ {n}} (0),
$$

where we are using conventions of Yano and Bochner [YB53] in Hermitian geometry.

THEOREM 7.7. For $\mu, \nu \in H^{-1,1}(\mathbb{D}^*)$ and $\kappa \in \Omega^{-1,1}(\mathbb{D}^*)$,

$$
\left. \frac {\partial^ {2}}{\partial \varepsilon \partial \bar {\varepsilon}} g _ {\mu \bar {\nu}} (\varepsilon \kappa) \right| _ {\varepsilon = 0} = \left(\mu \bar {\kappa}, G (\nu \bar {\kappa})\right) + \left(\mu \bar {\nu}, G (| \kappa | ^ {2})\right).
$$

PROOF. Differentiating the representation (7.7) for $g_{\mu \bar{\nu}}(\varepsilon \kappa)$ with respect to $\varepsilon$ and $\bar{\varepsilon}$ we get

$$
\begin{array}{r l} & {\left. \frac {\partial^ {2}}{\partial \varepsilon \partial \bar {\varepsilon}} g _ {\mu \bar {\nu}} (\varepsilon \kappa) \right| _ {\varepsilon = 0}} \\ & {= \left(\left. \frac {\partial^ {2}}{\partial \varepsilon \partial \bar {\varepsilon}} Q (\mu , \varepsilon \kappa) \right| _ {\varepsilon = 0}, \nu\right) + \left(\mu \bar {\nu}, \rho^ {- 1} \left. \frac {\partial^ {2}}{\partial \varepsilon \partial \bar {\varepsilon}} \rho^ {\varepsilon \kappa} \right| _ {\varepsilon = 0}\right)} \\ & {= \left(\left. \frac {\partial^ {2}}{\partial \varepsilon \partial \bar {\varepsilon}} Q (\mu , \varepsilon \kappa) \right| _ {\varepsilon = 0}, \nu\right) + \left(\left. \frac {\partial}{\partial \bar {\varepsilon}} \right| _ {\varepsilon = 0} Q (\mu , \varepsilon \kappa), \left. \frac {\partial}{\partial \bar {\varepsilon}} \right| _ {\varepsilon = 0} Q (\nu , \varepsilon \kappa)\right)} \\ & {+ \left(\mu , \left. \frac {\partial^ {2}}{\partial \varepsilon \partial \bar {\varepsilon}} Q (\nu , \varepsilon \kappa) \right| _ {\varepsilon = 0}\right) + \left(\mu \bar {\nu}, \rho^ {- 1} \left. \frac {\partial^ {2}}{\partial \varepsilon \partial \bar {\varepsilon}} \rho^ {\varepsilon \kappa} \right| _ {\varepsilon = 0}\right) - \left(\mu \bar {\nu}, | \kappa | ^ {2}\right).} \end{array}
$$

The differentiation under the integral sign is justified as in [Ahl62], provided that all integrals above are absolutely convergent. This follows from Proposition 6.3, property RK3 in Section 1.4, Proposition 7.2 and the following

LEMMA 7.8. For $\mu \in H^{-1,1}(\mathbb{D}^*)$ and $\nu \in \Omega^{-1,1}(\mathbb{D}^*)$,

$$
\left. \frac {\partial^ {2}}{\partial \varepsilon \partial \bar {\varepsilon}} Q (\mu , \varepsilon \nu) \right| _ {\varepsilon = 0} \in L ^ {2} (\mathbb {D} ^ {*}, \rho (z) d ^ {2} z).
$$

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

<!-- page 60 of 136 -->

7. RIEMANN CURVATURE TENSOR

51

PROOF. Here we prove Lemma 7.8. Using the model $\mathbb{H} \simeq \mathbb{U}$ and (1.25), we get for the second variation of $Q$,

$$
\left| \begin{array}{c}\frac {\partial^ {2}}{\partial \varepsilon \partial \bar {\varepsilon}} \bigg | _ {\varepsilon = 0} Q (\mu , \varepsilon \nu) (z) \\ = \frac {2 4}{\pi^ {3}} \iint_ {\mathbb {U}} \iint_ {\mathbb {U}} \iint_ {\mathbb {U}} \frac {\rho (z) ^ {- 1} \mu (w) \overline {{\nu (u)}} \nu (v) d ^ {2} v d ^ {2} u d ^ {2} w}{(w - v) ^ {2} (v - \bar {z}) ^ {2} (w - \bar {u}) ^ {2} (\bar {u} - \bar {z}) ^ {2}} \\ + \frac {2 4}{\pi^ {3}} \iint_ {\mathbb {U}} \iint_ {\mathbb {U}} \iint_ {\mathbb {U}} \frac {\rho (z) ^ {- 1} \mu (w) \overline {{\nu (u)}} \nu (v) d ^ {2} v d ^ {2} u d ^ {2} w}{(w - \bar {z}) ^ {2} (w - v) ^ {2} (v - \bar {u}) ^ {2} (\bar {u} - \bar {z}) ^ {2}} \\ + \frac {2 4}{\pi^ {3}} \iint_ {\mathbb {U}} \iint_ {\mathbb {U}} \iint_ {\mathbb {U}} \frac {\rho (z) ^ {- 1} \mu (w) \overline {{\nu (u)}} \nu (v) d ^ {2} v d ^ {2} u d ^ {2} w}{(w - \bar {z}) ^ {2} (w - \bar {u}) ^ {2} (v - \bar {u}) ^ {2} (v - \bar {z}) ^ {2}} \\ - \mu (z) \rho^ {- 1} (z) \left. \frac {\partial^ {2}}{\partial \varepsilon \partial \bar {\varepsilon}} \right| _ {\varepsilon = 0} \rho^ {\varepsilon \nu} (z) = I _ {1} (z) + I _ {2} (z) + I _ {3} (z) + I _ {4} (z). \end{array} \right|
$$

Using Proposition 6.3 and property RK3, we get that $I_4 \in L^2(\mathbb{U}, \rho(z)d^2z)$. Now using the Cauchy-Schwarz inequality, the identity

$$
\iint_ {\mathbb {U}} \frac {d ^ {2} w}{| w - \bar {z} | ^ {4}} = \frac {\pi}{4} \rho (z),
$$

and the property that the Hilbert transform is an isometry on $L^2(\mathbb{C}, d^2z)$, we get

$$
\begin{array}{l} \| I _ {1} \| _ {2} ^ {2} = \frac {2 4 ^ {2}}{\pi^ {6}} \iint_ {\mathbb {U}} \left| \iint_ {\mathbb {U}} \iint_ {\mathbb {U}} \iint_ {\mathbb {U}} \frac {\mu (w) \overline {{\nu (u)}} \nu (v) d ^ {2} v d ^ {2} u d ^ {2} w}{(w - v) ^ {2} (v - \bar {z}) ^ {2} (w - \bar {u}) ^ {2} (\bar {u} - \bar {z}) ^ {2}} \right| ^ {2} \rho (z) ^ {- 1} d ^ {2} z \\ \leq \frac {2 4 ^ {2}}{\pi^ {6}} \iint_ {\mathbb {U}} \left(\iint_ {\mathbb {U}} \frac {\rho (z) ^ {- 1} | \nu (v) | ^ {2} d ^ {2} v}{| v - \bar {z} | ^ {4}}\right) \\ \times \left(\iint_ {\mathbb {U}} \left| \iint_ {\mathbb {U}} \iint_ {\mathbb {U}} \frac {\mu (w) \overline {{\nu (u)}} d ^ {2} u d ^ {2} w}{(w - v) ^ {2} (w - \bar {u}) ^ {2} (\bar {u} - \bar {z}) ^ {2}} \right| ^ {2} d ^ {2} v\right) d ^ {2} z \\ \leq \frac {1 2 ^ {2} \| \nu \| _ {\infty} ^ {2}}{\pi^ {5}} \iint_ {\mathbb {U}} \iint_ {\mathbb {U}} \left| \iint_ {\mathbb {U}} \iint_ {\mathbb {U}} \frac {\mu (w) \overline {{\nu (u)}} d ^ {2} u d ^ {2} w}{(w - v) ^ {2} (w - \bar {u}) ^ {2} (\bar {u} - \bar {z}) ^ {2}} \right| ^ {2} d ^ {2} v d ^ {2} z \\ \leq \frac {1 2 ^ {2} \| \nu \| _ {\infty} ^ {2}}{\pi^ {3}} \iint_ {\mathbb {U}} \iint_ {\mathbb {U}} | \mu (v) | ^ {2} \left| \iint_ {\mathbb {U}} \frac {\nu (u) d ^ {2} u}{(u - \bar {v}) ^ {2} (u - z) ^ {2}} \right| ^ {2} d ^ {2} z d ^ {2} v \leq 3 6 \| \nu \| _ {\infty} ^ {4} \| \mu \| _ {2} ^ {2}. \end{array}
$$

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

<!-- page 61 of 136 -->

52

1. CURVATURE PROPERTIES AND CHERN FORMS

Similarly, denoting by $\overline{\mathbb{U}}$ the lower half-plane,

$$
\begin{array}{l} \| I _ {3} \| _ {2} ^ {2} = \frac {2 4 ^ {2}}{\pi^ {6}} \iint_ {\mathbb {U}} \left| \iint_ {\mathbb {U}} \iint_ {\mathbb {U}} \iint_ {\mathbb {U}} \frac {\mu (w) \overline {{\nu (u)}} \nu (v) d ^ {2} v d ^ {2} u d ^ {2} w}{(w - \bar {z}) ^ {2} (w - \bar {u}) ^ {2} (v - \bar {u}) ^ {2} (v - \bar {z}) ^ {2}} \right| ^ {2} \rho (z) ^ {- 1} d ^ {2} z \\ \leq \frac {1 2 ^ {2} \| \nu \| _ {\infty} ^ {2}}{\pi^ {5}} \iint_ {\mathbb {U}} \iint_ {\mathbb {U}} \left| \iint_ {\mathbb {U}} \iint_ {\mathbb {U}} \frac {\mu (w) \overline {{\nu (u)}} d ^ {2} u d ^ {2} w}{(w - \bar {z}) ^ {2} (w - \bar {u}) ^ {2} (v - \bar {u}) ^ {2}} \right| ^ {2} d ^ {2} v d ^ {2} z \\ = \frac {1 2 ^ {2} \| \nu \| _ {\infty} ^ {2}}{\pi^ {5}} \iint_ {\mathbb {U}} \iint_ {\overline {{\mathbb {U}}}} \left| \iint_ {\mathbb {U}} \iint_ {\mathbb {U}} \frac {\mu (w) \overline {{\nu (u)}} d ^ {2} u d ^ {2} w}{(w - \bar {z}) ^ {2} (w - \bar {u}) ^ {2} (\bar {v} - \bar {u}) ^ {2}} \right| ^ {2} d ^ {2} v d ^ {2} z \\ \leq \frac {1 2 ^ {2} \| \nu \| _ {\infty} ^ {2}}{\pi^ {3}} \iint_ {\mathbb {U}} \iint_ {\mathbb {U}} | \nu (v) | ^ {2} \left| \iint_ {\mathbb {U}} \frac {\mu (w) d ^ {2} w}{(w - \bar {z}) ^ {2} (w - \bar {v}) ^ {2}} \right| ^ {2} d ^ {2} v d ^ {2} z \\ \leq \frac {1 2 ^ {2} \| \nu \| _ {\infty} ^ {4}}{\pi} \iint_ {\mathbb {U}} \iint_ {\mathbb {U}} \frac {| \mu (v) | ^ {2}}{| v - \bar {z} | ^ {4}} d ^ {2} v d ^ {2} z = 3 6 \| \nu \| _ {\infty} ^ {4} \| \mu \| _ {2} ^ {2}. \end{array}
$$

For the term $I_{2}$ we use the same identity as in the proof of Proposition 6.3$^{5}$

$$
\begin{array}{r} \frac {1}{(v - \bar {u}) ^ {2} (\bar {u} - \bar {z}) ^ {2}} = \frac {(v - z) ^ {2}}{(v - \bar {z}) ^ {2} (z - \bar {u}) ^ {2} (v - \bar {u}) ^ {2}} + \frac {2 (v - z) ^ {2} (z - \bar {z})}{(v - \bar {z}) ^ {3} (v - \bar {u}) (z - \bar {u}) ^ {3}} \\ + \frac {(z - \bar {z}) ^ {2}}{(v - \bar {z}) ^ {2} (z - \bar {u}) ^ {2} (\bar {u} - \bar {z}) ^ {2}} + \frac {2 (z - \bar {z}) ^ {2} (v - z)}{(v - \bar {z}) ^ {3} (\bar {u} - \bar {z}) (\bar {u} - z) ^ {3}}. \end{array}
$$

As in the proof of Proposition 6.3, the last two terms do not contribute to $I_2$, and we obtain

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

$$
\begin{array}{r l} & I _ {2} (z) = \frac {2 4}{\pi^ {3}} \rho^ {- 1} (z) \iint_ {\mathbb {U}} \iint_ {\mathbb {U}} \iint_ {\mathbb {U}} \frac {\mu (w) \nu (v) \overline {{\nu (u)}} (v - z) ^ {2} d ^ {2} v d ^ {2} u d ^ {2} w}{(w - \bar {z}) ^ {2} (w - v) ^ {2} (v - \bar {z}) ^ {2} (z - \bar {u}) ^ {2} (v - \bar {u}) ^ {2}} \\ & \qquad + \frac {4 8}{\pi^ {3}} \rho^ {- 1} (z) \iint_ {\mathbb {U}} \iint_ {\mathbb {U}} \iint_ {\mathbb {U}} \frac {\mu (w) \nu (v) \overline {{\nu (u)}} (v - z) ^ {2} (z - \bar {z}) d ^ {2} v d ^ {2} u d ^ {2} w}{(w - \bar {z}) ^ {2} (w - v) ^ {2} (v - \bar {z}) ^ {3} (z - \bar {u}) ^ {3} (v - \bar {u})} \\ & \qquad = I _ {5} (z) + I _ {6} (z). \end{array}
$$

<small><span class="docvortex-page-footnote" data-block-type="page_footnote" style="color:#6b7280">$I_{2}$</span></small>

<small><span class="docvortex-page-footnote" data-block-type="page_footnote" style="color:#6b7280">$\nu \in \Omega^{-1,1}(\mathbb{U})$</span></small>

<small><span class="docvortex-page-footnote" data-block-type="page_footnote" style="color:#6b7280">$I_{1}$</span></small>

<small><span class="docvortex-page-footnote" data-block-type="page_footnote" style="color:#6b7280">$\nu \in H^{-1,1}(\mathbb{U})$</span></small>

<small><span class="docvortex-page-footnote" data-block-type="page_footnote" style="color:#6b7280">$^{5}$ We could estimate  $I_{2}$  in the same way as  $I_{1}$  If  $\nu \in H^{-1,1}(\mathbb{U})$ . However, for Theorem 8.5 we only have  $\nu \in \Omega^{-1,1}(\mathbb{U})$ .</span></small>

<!-- page 62 of 136 -->

7. RIEMANN CURVATURE TENSOR

53

The $L^2$-norm of $I_5$ is estimated exactly as before and we get $\| I_5\| _2^2\leq 36\| \nu \|_{\infty}^{4}\| \mu \|_{2}^{2}$. Finally,

$$
\begin{array}{l} \| I _ {6} \| _ {2} ^ {2} = \frac {4 8 ^ {2}}{\pi^ {6}} \iint_ {\mathbb {U}} \left| \iint_ {\mathbb {U}} \iint_ {\mathbb {U}} \iint_ {\mathbb {U}} \frac {\mu (w) \nu (v) \overline {{\nu (u)}} (v - z) ^ {2} (z - \bar {z}) d ^ {2} v d ^ {2} u d ^ {2} w}{(w - \bar {z}) ^ {2} (w - v) ^ {2} (v - \bar {z}) ^ {3} (z - \bar {u}) ^ {3} (v - \bar {u})} \right| ^ {2} \rho (z) ^ {- 1} d ^ {2} z \\ \leq \frac {2 4 ^ {2} \| \nu \| _ {\infty} ^ {2}}{\pi^ {5}} \iiint_ {\mathbb {U}} \iint_ {\mathbb {U}} \frac {| z - \bar {z} | ^ {2}}{| u - \bar {z} | ^ {2}} \left| \iiint_ {\mathbb {U}} \iint_ {\mathbb {U}} \frac {\mu (w) \nu (v) (v - z) ^ {2} d ^ {2} v d ^ {2} w}{(w - \bar {z}) ^ {2} (w - v) ^ {2} (v - \bar {z}) ^ {3} (v - \bar {u})} \right| ^ {2} d ^ {2} u d ^ {2} z \\ \leq \frac {2 4 ^ {2} \| \nu \| _ {\infty} ^ {2}}{\pi^ {5}} \iint_ {\mathbb {U}} \left(\iint_ {\mathbb {U}} \left| \iint_ {\mathbb {U}} \frac {\mu (w) d ^ {2} w}{(w - \bar {z}) ^ {2} (w - v) ^ {2}} \right| ^ {2} d ^ {2} v\right) \\ \left(\iint_ {\mathbb {U}} \frac {| z - \bar {z} | ^ {2}}{| u - \bar {z} | ^ {2}} \iint_ {\mathbb {U}} \frac {| \nu (v) | ^ {2} | v - z | ^ {4}}{| v - \bar {z} | ^ {6} | v - \bar {u} | ^ {2}} d ^ {2} v d ^ {2} u\right) d ^ {2} z. \end{array}
$$

Making a change of variables $\frac{v - z}{v - \bar{z}}\mapsto v$ and $\frac{u - z}{u - \bar{z}}\mapsto u$, we obtain

$$
\begin{array}{l l} \iint_ {\mathbb {U}} \frac {| z - \bar {z} | ^ {2}}{| u - \bar {z} | ^ {2}} \iint_ {\mathbb {U}} \frac {| \nu (v) | ^ {2} | v - z | ^ {4}}{| v - \bar {z} | ^ {6} | v - \bar {u} | ^ {2}} d ^ {2} v d ^ {2} u & \leq \| \nu \| _ {\infty} ^ {2} \iint_ {\mathbb {D}} \iint_ {\mathbb {D}} \frac {| v | ^ {4}}{| 1 - v \bar {u} | ^ {2}} d ^ {2} v d ^ {2} u \\ = \frac {3 \pi^ {2}}{4} \| \nu \| _ {\infty} ^ {2}. \end{array}
$$

Hence

$$
\| I _ {6} \| _ {2} ^ {2} \leq \frac {3 \cdot 1 2 ^ {2} \| \nu \| _ {\infty} ^ {4}}{\pi} \iint_ {\mathbb {U}} \iint_ {\mathbb {U}} \frac {| \mu (v) | ^ {2}}{| v - \bar {z} | ^ {4}} d ^ {2} v d ^ {2} z = 1 0 8 \| \nu \| _ {\infty} ^ {4} \| \mu \| _ {2} ^ {2}.
$$

Now comparing the two expressions for the second variation of $g_{\mu \bar{\nu}}$ and using Corollary 7.3 we get

$$
\begin{array}{c} \left(\mu , \frac {\partial^ {2}}{\partial \varepsilon \partial \bar {\varepsilon}} Q (\nu , \varepsilon \kappa) \Big | _ {\varepsilon = 0}\right) = - \left(\frac {\partial}{\partial \bar {\varepsilon}} \Big | _ {\varepsilon = 0} Q (\mu , \varepsilon \kappa), \frac {\partial}{\partial \bar {\varepsilon}} \Big | _ {\varepsilon = 0} Q (\nu , \varepsilon \kappa)\right) + \left(\mu \bar {\nu}, | \kappa | ^ {2}\right) \\ = (\mu \bar {\kappa}, G (\nu \bar {\kappa})). \end{array}
$$

Using Proposition 6.3, we finally obtain

$$
\left. \frac {\partial^ {2}}{\partial \varepsilon \partial \bar {\varepsilon}} \right| _ {\varepsilon = 0} g _ {\mu \bar {\nu}} (\varepsilon \kappa) = \left(\mu \bar {\kappa}, G (\nu \bar {\kappa})\right) + \left(\mu \bar {\nu}, G (| \kappa | ^ {2})\right).
$$

COROLLARY 7.9. At the origin of $T(1)$,

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

$$
R _ {k \bar {l} m \bar {n}} = - \left(\mu_ {k} \bar {\mu} _ {l}, G (\bar {\mu} _ {m} \mu_ {n})\right) - \left(\bar {\mu} _ {l} \mu_ {m}, G (\bar {\mu} _ {k} \mu_ {n})\right).
$$

PROOF. It follows from Theorem 7.7 by polarization that

$$
\begin{array}{c} R _ {\kappa \bar {\lambda} \mu \bar {\nu}} = - \left. \frac {\partial^ {2}}{\partial \varepsilon_ {1} \partial \bar {\varepsilon} _ {2}} \right| _ {\varepsilon_ {1} = \varepsilon_ {2} = 0} g _ {\mu \bar {\nu}} (\varepsilon_ {1} \kappa + \varepsilon_ {2} \lambda) \\ = - (\kappa \bar {\lambda}, G (\bar {\mu} \nu)) - (\bar {\lambda} \mu , G (\bar {\kappa} \nu)). \end{array}
$$

<!-- page 63 of 136 -->

54

1. CURVATURE PROPERTIES AND CHERN FORMS

REMARK 7.10. For finite-dimensional Teichmüller spaces this result was proved by Wolpert [Wol86]. Except Lemma 7.8, our derivation is the same as in [Wol86].

7.3. Ricci and sectional curvatures. The Ricci tensor at the origin of $T(1)$ for the orthonormal basis $\{\mu_n\}_{n=2}^{\infty}$ of $H^{-1,1}(\mathbb{D}^*)$ is defined by the following series

$$
\mathcal {R} _ {k \bar {l}} = \sum_ {n = 2} ^ {\infty} R _ {k \bar {n} n \bar {l}}.
$$

THEOREM 7.11. The Ricci tensor at the origin of $T(1)$ is well-defined and is given by

$$
\mathcal {R} _ {k \bar {l}} = - \frac {1 3}{1 2 \pi} \delta_ {k l}.
$$

PROOF. Set $\mu = \mu_{k},\nu = \mu_{l}$, and $\mathcal{R}_{\mu \bar{\nu}} = \mathcal{R}_{k\bar{l}}$. We have

$$
\begin{array}{c} \mathcal {R} _ {\mu \bar {\nu}} = - \frac {2}{\pi} \sum_ {n = 2} ^ {\infty} (n ^ {3} - n) \left(\iint_ {\mathbb {D} ^ {*}} \iint_ {\mathbb {D} ^ {*}} G (z, w) \mu (z) z ^ {n - 2} \overline {{\nu (w)}} \bar {w} ^ {n - 2} d ^ {2} w d ^ {2} z \right. \\ \left. + \iint_ {\mathbb {D} ^ {*}} \iint_ {\mathbb {D} ^ {*}} G (z, w) \bar {z} ^ {n - 2} z ^ {n - 2} \mu (w) \overline {{\nu (w)}} \frac {(1 - | z | ^ {2}) ^ {2}}{(1 - | w | ^ {2}) ^ {2}} d ^ {2} w d ^ {2} z\right) \\ = - \frac {1 2}{\pi} \iint_ {\mathbb {D} ^ {*}} \iint_ {\mathbb {D} ^ {*}} G (z, w) \frac {\mu (z) \overline {{\nu (w)}}}{(1 - z \bar {w}) ^ {4}} d ^ {2} w d ^ {2} z \\ - \frac {3}{4 \pi} \iint_ {\mathbb {D} ^ {*}} \iint_ {\mathbb {D} ^ {*}} G (z, w) \mu (w) \overline {{\nu (w)}} \rho (z) \rho (w) d ^ {2} w d ^ {2} z \\ = I _ {1} + I _ {2}. \end{array}
$$

For the second integral, we use property RK4 in Section 1.4 and get

$$
I _ {2} = - \frac {3}{4 \pi} \iint_ {\mathbb {D}} \mu (w) \overline {{\nu (w)}} \rho (w) d ^ {2} w = - \frac {3}{4 \pi} g _ {\mu \bar {\nu}}.
$$

For the first integral, we use projection formula (1.7) and get

$$
I _ {1} = - \frac {3 6}{\pi^ {2}} \iint_ {\mathbb {D} ^ {*}} \iint_ {\mathbb {D} ^ {*}} \iint_ {\mathbb {D} ^ {*}} G (z, w) \mu (z) \overline {{\nu (v)}} \frac {(1 - | w | ^ {2}) ^ {2}}{(1 - z \bar {w}) ^ {4} (1 - w \bar {v}) ^ {4}} d ^ {2} v d ^ {2} w d ^ {2} z.
$$

Let

$$
B (z, v) = \iint_ {\mathbb {D} ^ {*}} G (z, w) \frac {(1 - | w | ^ {2}) ^ {2}}{(1 - w \bar {v}) ^ {4} (1 - z \bar {w}) ^ {4}} d ^ {2} w.
$$


> **[ERRATUM W1-04]** (3053–3082; Lean: `bKernel`, `eq_7_8` (S7_Curvature, "Readings")) Domain misprint: 0 ∉ 𝔻*, and G(0,·) is the 𝔻 resolvent kernel at the centre. The computation is the 𝔻 one, which is model-independent by PSU(1,1)-covariance plus inversion. It should read ∬_𝔻 (or be transported by z ↦ 1/z̄).

The kernel $B(z,v)$ satisfies

(7.8)

$$
B (z, v) = B \Big (\sigma z, \sigma v \Big) \sigma^ {\prime} (z) ^ {2} \overline {{\sigma^ {\prime} (v)}} ^ {2} \quad \text {for all} \quad \sigma \in \mathrm{PSU} (1, 1),
$$

and

$$
B (0, v) = \iint_ {\mathbb {D} ^ {*}} \left(\frac {1}{2 \pi} \frac {1 + | w | ^ {2}}{1 - | w | ^ {2}} \log \frac {1}{| w | ^ {2}} - \frac {1}{\pi}\right) \frac {(1 - | w | ^ {2}) ^ {2}}{(1 - \bar {v} w) ^ {4}} d ^ {2} w = \frac {1}{9}.
$$

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

<!-- page 64 of 136 -->

7. RIEMANN CURVATURE TENSOR

55

Hence

$$
B (z, v) = \frac {1}{9 (1 - z \bar {v}) ^ {4}}
$$

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026for download from IP 130.34.46.51.

and

$$
\begin{array}{r l} & I _ {1} = - \frac {4}{\pi^ {2}} \iint_ {\mathbb {D} ^ {*}} \iint_ {\mathbb {D} ^ {*}} \mu (z) \overline {{\nu (v)}} \frac {1}{(1 - z \bar {v}) ^ {4}} d ^ {2} z d ^ {2} w \\ & \qquad = - \frac {1}{3 \pi} \iint_ {\mathbb {D} ^ {*}} \mu (z) \overline {{\nu (z)}} \rho (z) d ^ {2} z = - \frac {1}{3 \pi} g _ {\mu \bar {\nu}}. \end{array}
$$


> **[ERRATUM W1-05]** (3089; Lean: proof of `thm_7_11` (S7_Curvature)) Misprint: the measure is d²z d²v (w was already integrated out into B). The value −(1/3π) g is correct: −36/π² · 1/9 = −4/π², and the reproducing formula (1.7) gives π ρ ν̄/12.

Therefore.

$$
\mathcal {R} _ {\mu \bar {\nu}} = - \left(\frac {3}{4 \pi} + \frac {1}{3 \pi}\right) g _ {\mu \bar {\nu}} = - \frac {1 3}{1 2 \pi} g _ {\mu \bar {\nu}}.
$$

Since the Weil-Petersson metric on $T(1)$ is right-invariant, it follows from Theorem 7.11 that the Ricci tensor is well-defined everywhere on $T(1)$. Denote by $Ric_{WP}$ corresponding Ricci (1,1)-form on $T(1)$. In terms of Bers coordinates $\{\varepsilon_n\}_{n=2}^{\infty}$ on the coordinate chart $V_{\mu}$ the Ricci form is given by

$$
R i c _ {W P} = \frac {i}{2} \sum_ {k, l = 2} ^ {\infty} \mathcal {R} _ {k \bar {l}} d \varepsilon_ {k} \wedge d \bar {\varepsilon} _ {l}.
$$

COROLLARY 7.12. The universal Teichmüller space $T(1)$ is a Kähler-Einstein manifold with negative constant Ricci curvature,

$$
R i c _ {W P} = - \frac {1 3}{1 2 \pi} \omega_ {W P}.
$$

PROOF. Since $(1,1)$- forms $\omega_{WP}$ and $Ric$ are right-invariant, the result immediately follows from Theorem 7.11

REMARK 7.13. For the dense submanifold $\mathrm{Möb}(S^1) \backslash \mathrm{Diff}_+(S^1)$ of $T_0(1)$ the statement of Theorem 7.11 was established by different methods in [KY87] and [BR87a, BR87b]. The "magic ratio" $\frac{13}{12\pi}$ is omnipresent in mathematics and in the string theory.

Let $\frac{\partial}{\partial t_{\mu}}, \frac{\partial}{\partial t_{\nu}} \in T_0^{\mathbb{R}}T(1)$ be real tangent vectors. According to [YB53], the sectional curvature of the section spanned by these vectors is given by $R / g$, where

$$
R = R _ {\mu \bar {\nu} \nu \bar {\mu}} + R _ {\nu \bar {\mu} \mu \bar {\nu}} - R _ {\mu \bar {\nu} \mu \bar {\nu}} - R _ {\nu \bar {\mu} \nu \bar {\mu}},\tag{7.9}
$$

$$
g = 4 g _ {\mu \bar {\mu}} g _ {\nu \bar {\nu}} - 2 | g _ {\mu \bar {\nu}} | ^ {2} - 2 \mathrm{Re} (g _ {\mu \bar {\nu}}) ^ {2}.
$$

Similarly, the holomorphic sectional curvature of the section spanned by the holomorphic tangent vector $\frac{\partial}{\partial\varepsilon_{\mu}}$, where $g_{\mu \bar{\mu}} = 1$, is given by $R_{\mu \bar{\mu}\mu \bar{\mu}}$.

As in the finite-dimensional case [Wol86], we have

THEOREM 7.14. The sectional and holomorphic sectional curvatures of $T(1)$ are negative.


> **[ERRATUM W1-07]** (3128–3156; Lean: `thm_7_14` (S7_Curvature)) Proof gap, not a false claim: the two inequalities give only R ≤ 0. Strictness needs the equality case: (β,Gβ) = 0 ⇒ β = 0 (with μν̄ = α + iβ), and Cauchy–Schwarz equality ⇒ \|μ\| = c\|ν\|. Together with μν̄ real this gives μ = ±cν on the connected 𝔻*, contradicting ℝ-independence. The statement is true.

<!-- page 65 of 136 -->

56

1. CURVATURE PROPERTIES AND CHERN FORMS

PROOF. For a section spanned by $\frac{\partial}{\partial\varepsilon_{\mu}}$, the holomorphic sectional curvature is obviously negative: $\mu \neq 0$ so that $G(|\mu|^2) > 0$, and $(|\mu|^2, G(|\mu|^2)) > 0$.

For a section spanned by the real tangent vectors $\frac{\partial}{\partial t_{\mu}}$ and $\frac{\partial}{\partial t_{\nu}}$, using Cauchy-Schwarz inequality, it is easy to see that $g$ is positive. Using Corollary 7.9, the properties RK1 and RK2, we get

$$
R = 4 \mathrm{Re} (\mu \bar {\nu}, G (\bar {\mu} \nu)) - 2 (\mu \bar {\nu}, G (\mu \bar {\nu})) - 2 (| \mu | ^ {2}, G (| \nu | ^ {2})).
$$

From the property RK2 and Cauchy-Schwarz inequality we have

$$
\begin{array}{c} | G (\mu \bar {\nu}) (z) | \leq \iint_ {\mathbb {D} ^ {*}} G (z, w) ^ {1 / 2} | \mu (w) | G (z, w) ^ {1 / 2} | \nu (w) | \rho (w) d ^ {2} w \\ \leq \left(\iint_ {\mathbb {D} ^ {*}} G (z, w) | \mu (w) | ^ {2} \rho (w) d ^ {2} w\right) ^ {1 / 2} \left(\iint_ {\mathbb {D} ^ {*}} G (z, w) | \nu (w) | ^ {2} \rho (w) d ^ {2} w\right) ^ {1 / 2} \end{array}
$$

so that

$$
\begin{array}{l} | (\bar {\mu} \nu , G (\mu \bar {\nu})) | \leq \iint_ {\mathbb {D} ^ {*}} | \mu \nu | G (| \mu | ^ {2}) ^ {1 / 2} G (| \nu | ^ {2}) ^ {1 / 2} \rho (z) d ^ {2} z \\ \qquad \qquad \qquad \leq \left(\iint_ {\mathbb {D} ^ {*}} | \mu | ^ {2} G (| \nu | ^ {2}) \rho (z) d ^ {2} z\right) ^ {1 / 2} \left(\iint_ {\mathbb {D} ^ {*}} | \nu | ^ {2} G (| \mu | ^ {2}) \rho (z) d ^ {2} z\right) ^ {1 / 2} \\ \qquad \qquad = \big (| \mu | ^ {2}, G (| \nu | ^ {2}) \big). \end{array}
$$

On the other hand, if we let $\mu \bar{\nu} = \alpha + i\beta$, where $\alpha$ and $\beta$ are real-valued functions, then $\operatorname{Re}(\mu \bar{\nu}, G(\bar{\mu}\nu)) = (\alpha, G(\alpha)) - (\beta, G(\beta))$ and $(\mu \bar{\nu}, G(\mu \bar{\nu})) = (\alpha, G(\alpha)) + (\beta, G(\beta))$. Since for a bounded real-valued smooth function $h$, we can deduce from the property RK3 and the positivity of the operator $\Delta_0 + \frac{1}{2}$ that $(h, G(h)) \geq 0$, it follows that $\operatorname{Re}(\mu \bar{\nu}, G(\bar{\mu}\nu)) \leq (\mu \bar{\nu}, G(\mu \bar{\nu}))$. Hence $R$ is negative by Cauchy-Schwarz inequality.

## 8. Finite-dimensional Teichmüller spaces

Curvature properties of finite-dimensional Teichmüller spaces were extensively studied by Ahlfors [Ahl62], Royden [Roy75], and especially by Wolpert [Wol86]. Here, for the Teichmüller space $T(\Gamma)$ of a cofinite Fuchsian group $\Gamma$ we show how to get Wolpert's explicit formulas from the curvature formulas of the Hilbert manifold $T(1)$, derived in Section 7.

First note that the canonical embedding of the finite-dimensional complex manifold $T(\Gamma)$ into $T(1)$ is holomorphic with respect to the Banach manifold structure on $T(1)$ but not with respect to the Hilbert manifold structure on $T(1)$. Indeed, for a cofinite Fuchsian group $\Gamma$ the finite-dimensional vector space $\Omega^{-1,1}(\mathbb{D}^*,\Gamma)$ is not a subspace of the Hilbert space $H^{-1,1}(\mathbb{D}^*)$, but rather

$$
\Omega^ {- 1, 1} (\mathbb {D} ^ {*}, \Gamma) \cap H ^ {- 1, 1} (\mathbb {D} ^ {*}) = \{0 \}.
$$

Thus the Weil-Petersson metric on  $T(\Gamma)$ , defined in Section 1.3, is not a pullback of the Weil-Petersson metric on  $T(1)$ . However, due to Lemma 1.9 we can represent the Petersson inner product on the tangent space at the origin of  $T(\Gamma)$  as an “average” of the inner products in  $T(1)$ . Namely, using the canonical complex

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

<!-- page 66 of 136 -->

8. FINITE-DIMENSIONAL TEICHMÜLLER SPACES

57

anti-linear isomorphisms $\Omega^{-1,1}(\mathbb{D}^*,\Gamma)\simeq \Omega^{-1,1}(\mathbb{D},\Gamma)$ and $H^{-1,1}(\mathbb{D}^*)\simeq H^{-1,1}(\mathbb{D})$, we have

$$
\begin{array}{c} \langle \mu , \nu \rangle_ {W P} = \iint_ {\Gamma \backslash \mathbb {D}} \mu \bar {\nu} \rho (z) d ^ {2} z = \lim _ {r \to 1 ^ {-}} \frac {A (\Gamma \backslash \mathbb {D})}{A (\mathbb {D} _ {r})} \iint_ {\mathbb {D} _ {r}} \mu \bar {\nu} \rho (z) d ^ {2} z \\ = \lim _ {r \to 1 ^ {-}} \frac {A (\Gamma \backslash \mathbb {D})}{A (\mathbb {D} _ {r})} \iint_ {\mathbb {D}} \mu_ {r} \bar {\nu} _ {r} \rho (z) d ^ {2} z. \end{array}
$$

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

Here $\mu, \nu \in \Omega^{-1,1}(\mathbb{D}, \Gamma)$ and $\mu_r = \chi_r \mu, \nu_r = \chi_r \nu$, where $\chi_r$ is the characteristic function of $\mathbb{D}_r = \{z \in \mathbb{D} : |z| \leq r\}$. In what follows we will denote by $(, )_\Gamma$ the Petersson inner product $\langle , \rangle_{WP}$ in $\Omega^{-1,1}(\mathbb{D}, \Gamma)$, as well as the inner product for the Hilbert space $L^2(\Gamma \backslash \mathbb{D}, \rho(z)d^2 z)$. Since they are given by the same formula, there would be no confusion. Moreover, for $\mu \in \Omega^{-1,1}(\mathbb{D}, \Gamma)$, $|\mu| \in L^2(\Gamma \backslash \mathbb{D}, \rho(z)d^2 z)$.

LEMMA 8.1. Let $\mu \in \Omega^{-1,1}(\mathbb{D})$ and $\nu \in L^{\infty}(\mathbb{D})\cap L^{1}(\mathbb{D},\rho (z)d^{2}z)$. Then

(i) For $0 < r < 1$,

$$
P (\mu_ {r}) \in H ^ {- 1, 1} (\mathbb {D}) \text {and} P (\mu_ {r}) (z) = O \left((1 - | z | ^ {2}) ^ {2}\right) \text {as} | z | \rightarrow 1.
$$

(ii)

$$
\lim _ {r \to 1 ^ {-}} \iint_ {\mathbb {D}} P (\mu_ {r}) \bar {\nu} \rho (z) d ^ {2} z = \iint_ {\mathbb {D}} \mu \bar {\nu} \rho (z) d ^ {2} z.
$$

PROOF. Since

$$
\iint_ {\mathbb {D}} \left| P \left(\mu_ {r}\right) \right| ^ {2} \rho (z) d ^ {2} z = \iint_ {\mathbb {D}} P \left(\mu_ {r}\right) \bar {\mu} _ {r} \rho (z) d ^ {2} z = \iint_ {\mathbb {D} _ {r}} P \left(\mu_ {r}\right) \bar {\mu} _ {r} \rho (z) d ^ {2} z <   \infty ,
$$

$P(\mu_r) \in H^{-1,1}(\mathbb{D})$. Using $\mu(z) = -\frac{(1 - |z|^2)^2}{2}\sum_{n=2}^{\infty}(n^3 - n)a_n\bar{z}^{n-2}$ and (1.7), we get

$$
P (\mu_ {r}) (z) = - \frac {(1 - | z | ^ {2}) ^ {2}}{4} \sum_ {n = 2} ^ {\infty} (n ^ {3} - n) a _ {n} \left(\frac {r ^ {2 n + 2}}{n + 1} - \frac {2 r ^ {2 n}}{n} + \frac {r ^ {2 n - 2}}{n - 1}\right) \bar {z} ^ {n - 2},
$$

so that $(1 - |z|^2)^{-2}P(\mu_r)(z)$ is continuous on $|z| = 1$.

To prove part (ii), consider the estimate

$$
\begin{array}{r l} & {| (\mu - P (\mu_ {r})) (z) | \leq \frac {3 (1 - | z | ^ {2}) ^ {2}}{\pi} \| \mu \| _ {\infty} \iint_ {\mathbb {D} \setminus \mathbb {D} _ {r}} \frac {d ^ {2} u}{| 1 - u \bar {z} | ^ {4}}} \\ & {\qquad = 3 \| \mu \| _ {\infty} (1 - | z | ^ {2}) ^ {2} \sum_ {n = 1} ^ {\infty} n | z | ^ {2 n - 2} (1 - r ^ {2 n})} \\ & {\qquad = 3 \| \mu \| _ {\infty} \left(1 - \frac {r ^ {2} (1 - | z | ^ {2}) ^ {2}}{(1 - r ^ {2} | z | ^ {2}) ^ {2}}\right).} \end{array}
$$

For fixed $r$ the right hand side of this estimate is an increasing function of $|z|$, so that

$$
\sup _ {| z | \leq s} \left| (\mu - P (\mu_ {r})) (z) \right| \leq 3 \| \mu \| _ {\infty} \left(1 - \frac {r ^ {2} (1 - s ^ {2}) ^ {2}}{(1 - r ^ {2} s ^ {2}) ^ {2}}\right),
$$

and for fixed $s$,

$$
\lim _ {r \to 1 ^ {-}} \sup _ {| z | \leq s} | (\mu - P (\mu_ {r})) (z) | = 0.
$$

<!-- page 67 of 136 -->

58

1. CURVATURE PROPERTIES AND CHERN FORMS

Also for fixed $r$ we have the estimate

$$
\| \mu - P (\mu_ {r}) \| _ {\infty} \leq 3 \| \mu \| _ {\infty}.
$$

Now since $\nu \in L^{1}(\mathbb{D},\rho (z)d^{2}z)$, for every $\varepsilon >0$ there exists $0 < s < 1$ such that

$$
\iint_ {\mathbb {D} \backslash \mathbb {D} _ {s}} | \nu | \rho (z) d ^ {2} z \leq \varepsilon ,
$$

and we obtain,

$$
\begin{array}{c} \hline \left| \iint_ {\mathbb {D}} (\mu - P (\mu_ {r}))   \bar {\nu} \rho (z) d ^ {2} z \right| \\ \leq \iint_ {\mathbb {D} _ {s}} | (\mu - P (\mu_ {r})) |   | \nu |   \rho (z) d ^ {2} z + \iint_ {\mathbb {D} \setminus \mathbb {D} _ {s}} | (\mu - P (\mu_ {r})) |   | \nu |   \rho (z) d ^ {2} z \\ \leq \sup _ {| z | \leq s} | (\mu - P (\mu_ {r}))   (z) | \iint_ {\mathbb {D}} | \nu |   \rho (z) d ^ {2} z + 3 \varepsilon \| \mu \| _ {\infty}. \\ \hline \end{array}
$$

Passing to the limit $r\to 1^{-}$ , we get

$$
\varliminf_ {r \to 1 ^ {-}} \left| \iint_ {\mathbb {D}} \left(\mu - P (\mu_ {r})\right) \bar {\nu}   \rho (z) d ^ {2} z \right| \leq 3 \varepsilon \| \mu \| _ {\infty}.
$$

Since $\varepsilon$ is arbitrary, the result follows.

LEMMA 8.2. For $\mu, \nu \in \Omega^{-1,1}(\mathbb{D}, \Gamma)$,

$$
(\mu , \nu) _ {\Gamma} = \lim _ {r \to 1 ^ {-}} \lim _ {s \to 1 ^ {-}} \frac {A (\Gamma \backslash \mathbb {D})}{A (\mathbb {D} _ {r})} \iint_ {\mathbb {D}} P (\mu_ {s}) \overline {{P (\nu_ {r})}} \rho (z) d ^ {2} z.
$$

PROOF. Since $\mu \in \Omega^{-1,1}(\mathbb{D},\Gamma)\subset \Omega^{-1,1}(\mathbb{D})$,

$$
\iint_ {\mathbb {D}} \mu_ {r} \bar {\nu} _ {r} \rho (z) d ^ {2} z = \iint_ {\mathbb {D}} \mu \bar {\nu} _ {r} \rho (z) d ^ {2} z = \iint_ {\mathbb {D}} \mu \overline {{P (\nu_ {r})}} \rho (z) d ^ {2} z.
$$

According to part (i) of Lemma 8.1, $P(\nu_r) \in L^1(\mathbb{D}, \rho(z)d^2z)$ for $0 < r < 1$, so that the result follows from part (ii) of Lemma 8.1.

REMARK 8.3. The limits in Lemma 8.2 can not be interchanged. Indeed, it follows from part (ii) of Lemma 8.1 that for fixed $s < 1$ the limit $r \to 1$ is always zero.

In a neighborhood of the origin in $T(\Gamma)$ the Weil-Petersson metric is given by

$$
g _ {\mu \bar {\nu}} (\kappa) = \iint_ {\Gamma_ {\kappa} \backslash \mathbb {D}} P (R (\mu , \kappa)) \overline {{P (R (\nu , \kappa))}} \rho (z) d ^ {2} z,
$$


> **[IMPLICIT HYPOTHESIS 8-6]** (3285, 1322; Lean: S8 model, `wD`) The memoir does not fix the normalization in the 𝔻 model; Γ_κ = w_κΓw_κ⁻¹ depends on it only by conjugation.

where $\kappa \in \Omega^{-1,1}(\mathbb{D},\Gamma)$, $\| \kappa \|_{\infty}$ is sufficiently small, and $\Gamma_{\kappa} = w_{\kappa}\circ \Gamma \circ w_{\kappa}^{-1}$.

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

<!-- page 68 of 136 -->

8. FINITE-DIMENSIONAL TEICHMÜLLER SPACES

59

LEMMA 8.4. Let $\mu, \nu \in \Omega^{-1,1}(\mathbb{D}, \Gamma)$. For $\kappa \in \Omega^{-1,1}(\mathbb{D}, \Gamma)$, $\| \kappa \|_{\infty}$ sufficiently small,

$$
g _ {\mu \bar {\nu}} (\kappa) = \lim _ {r \to 1 ^ {-}} \lim _ {s \to 1 ^ {-}} \frac {A (\Gamma \backslash \mathbb {D})}{A (\mathbb {D} _ {r})} \iint_ {\mathbb {D}} P (R (P (\mu_ {s}), \kappa)) \overline {{P (R (P (\nu_ {r}) , \kappa))}} \rho (z) d ^ {2} z.
$$

PROOF. First, we have

$$
\begin{array}{c} \int_ {\mathbb {D}} P (R (P (\mu_ {s}), \kappa)) \overline {{P (R (P (\nu_ {r}) , \kappa))}} \rho (z) d ^ {2} z \\ = \frac {1 2}{\pi} \iint_ {\mathbb {D}} \iint_ {\mathbb {D}} \frac {P (\mu_ {s}) (u) (w _ {\kappa}) _ {u} (u) ^ {2} \overline {{P (\nu_ {r}) (z) (w _ {\kappa}) _ {z} (z) ^ {2}}}}{(1 - w _ {\kappa} (u) \overline {{w _ {\kappa} (z)}}) ^ {4}} d ^ {2} z d ^ {2} u. \end{array}
$$

Since $\rho P(\nu_r)$ is bounded on $\mathbb{D}$, and for $\| \kappa \|_{\infty}$ sufficiently small $(1/2)\rho \leq w_{\kappa}^{*}\rho \leq (3/2)\rho$, we conclude that $\rho R(P(\nu_r), \kappa)$ is also bounded on $\mathbb{D}$. As a result,

$$
\begin{array}{l} \iint_ {\mathbb {D}} \left| \iint_ {\mathbb {D}} \frac {(w _ {\kappa}) _ {u} (u) ^ {2} \overline {{P (\nu_ {r}) (z) (w _ {\kappa}) _ {z} (z) ^ {2}}}}{(1 - w _ {\kappa} (u) \overline {{w _ {\kappa} (z)}}) ^ {4}} d ^ {2} z \right| d ^ {2} u \\ = \iint_ {\mathbb {D}} \left| \iint_ {\mathbb {D}} \frac {\overline {{R (P (\nu_ {r}) , \kappa) (z)}}}{(1 - u \bar {z}) ^ {4}} d ^ {2} z \right| \frac {d ^ {2} u}{1 - | \kappa (u) | ^ {2}} \\ \leq C \iint_ {\mathbb {D}} \iint_ {\mathbb {D}} \frac {(1 - | z | ^ {2}) ^ {2}}{| 1 - u \bar {z} | ^ {4}} d ^ {2} z d ^ {2} u = \pi^ {2} C <   \infty . \end{array}
$$

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

It follows from part (ii) of Lemma 8.1 that

$$
\left| \begin{array}{l} \underset {s \to 1 ^ {-}} {\lim} \iint_ {\mathbb {D}} P (R (P (\mu_ {s}), \kappa)) \overline {{P (R (P (\nu_ {r}) , \kappa))}} \rho (z) d ^ {2} z \\ = \frac {1 2}{\pi} \iint_ {\mathbb {D}} \iint_ {\mathbb {D}} \frac {\mu (u) (w _ {\kappa}) _ {u} (u) ^ {2} \overline {{P (\nu_ {r}) (z) (w _ {\kappa}) _ {z} (z) ^ {2}}}}{(1 - w _ {\kappa} (u) \overline {{w _ {\kappa} (z)}}) ^ {4}} d ^ {2} z d ^ {2} u \\ = \iint_ {\mathbb {D}} P (R (\mu , \kappa)) \overline {{P (R (P (\nu_ {r}) , \kappa))}} \rho (z) d ^ {2} z. \end{array} \right.
$$

Now

$$
\begin{array}{c} \iint_ {\mathbb {D}} P (R (\mu , \kappa)) \overline {{P (R (P (\nu_ {r}) , \kappa))}} \rho (z) d ^ {2} z \\ = \frac {1 4 4}{\pi^ {2}} \iint_ {\mathbb {D}} \iint_ {\mathbb {D} _ {r}} \iint_ {\mathbb {D}} \frac {\mu (u) (w _ {\kappa}) _ {u} (u) ^ {2} \overline {{\nu (v) (w _ {\kappa}) _ {z} (z) ^ {2}}}}{(1 - w _ {\kappa} (u) \overline {{w _ {\kappa} (z)}}) ^ {4} (1 - z \bar {v}) ^ {4}} \rho (z) ^ {- 1} d ^ {2} u d ^ {2} v d ^ {2} z \\ = \frac {1 4 4}{\pi^ {2}} \iint_ {\mathbb {D} _ {r}} \lambda (v) \overline {{\nu (v)}} \rho (v) d ^ {2} v, \end{array}
$$

where

$$
\lambda (v) = \rho (v) ^ {- 1} \iint_ {\mathbb {D}} \iint_ {\mathbb {D}} \frac {\mu (u) (w _ {\kappa}) _ {u} (u) ^ {2} \overline {{(w _ {\kappa}) _ {z} (z) ^ {2}}} \rho (z) ^ {- 1}}{(1 - w _ {\kappa} (u) w _ {\kappa} (z)) ^ {4} (1 - z \bar {v}) ^ {4}} d ^ {2} u d ^ {2} z.
$$

<!-- page 69 of 136 -->

60

1. CURVATURE PROPERTIES AND CHERN FORMS

Since $\mu \in \Omega^{-1,1}(\mathbb{D},\Gamma)$ and $w_{\kappa}\circ \Gamma \circ w_{\kappa}^{-1} = \Gamma_{\kappa}\subseteq \mathrm{PSU}(1,1)$, it is easy to see that $\lambda \in \Omega^{-1,1}(\mathbb{D},\Gamma)$. Using Lemma 1.9, we get

$$
\begin{array}{c} \underset {r \to 1 ^ {-}} {\lim} \frac {A (\Gamma \backslash \mathbb {D})}{A (\mathbb {D} _ {r})} \iint_ {\mathbb {D}} P (R (\mu , \kappa)) \overline {{P (R (P (\nu_ {r}) , \kappa))}} \rho (z) d ^ {2} z \\ = \frac {1 4 4}{\pi^ {2}} \iint_ {\Gamma \backslash \mathbb {D}} \lambda (v) \overline {{\nu (v)}} \rho (v) d ^ {2} v \\ = \frac {1 4 4}{\pi^ {2}} \iint_ {\mathbb {D}} \iint_ {\Gamma \backslash \mathbb {D}} \iint_ {\mathbb {D}} \frac {\mu (u) (w _ {\kappa}) _ {u} (u) ^ {2} \overline {{\nu (v) (w _ {\kappa}) _ {z} (z) ^ {2}}}}{(1 - w _ {\kappa} (u) \overline {{w _ {\kappa} (z)}}) ^ {4} (1 - z \bar {v}) ^ {4}} \rho (z) ^ {- 1} d ^ {2} u d ^ {2} v d ^ {2} z \\ = \frac {1 4 4}{\pi^ {2}} \iint_ {\Gamma \backslash \mathbb {D}} \iint_ {\mathbb {D}} \iint_ {\mathbb {D}} \frac {\mu (u) (w _ {\kappa}) _ {u} (u) ^ {2} \overline {{\nu (v) (w _ {\kappa}) _ {z} (z) ^ {2}}}}{(1 - w _ {\kappa} (u) \overline {{w _ {\kappa} (z)}}) ^ {4} (1 - z \bar {v}) ^ {4}} \rho (z) ^ {- 1} d ^ {2} u d ^ {2} v d ^ {2} z \\ = \iint_ {\Gamma \backslash \mathbb {D}} P (R (\mu , \kappa)) \overline {{P (R (\nu , \kappa))}} \rho (z) d ^ {2} z, \end{array}
$$

where we have used the fact that the integrals above do not change if we let any one of the integration variables to range over $\Gamma \backslash \mathbb{D}$ while others range over $\mathbb{D}$ (cf. [Ahl62]). The latter property follows from the fact that $\mu, \nu$ and $\kappa$ are $(-1, 1)$ tensors for $\Gamma$, and the representation $\mathbb{D} = \bigcup_{\gamma \in \Gamma} \gamma(\Gamma \backslash \mathbb{D})$.

THEOREM 8.5. For $\mu, \nu, \kappa \in \Omega^{-1,1}(\mathbb{D}, \Gamma)$,


> **[IMPLICIT HYPOTHESIS 8-4]** (3350–3356; Lean: `thm_8_5`, `eq_8_1`, S8) The memoir assumes, without proof, that ε ↦ g_{μν̄}(εκ) is C² and that the derivatives commute with the double limit. In Lean, clause 1 (`dz … = 0`) would also hold for junk (non-differentiable) values. Suggest the D7 pattern: add `DifferentiableAt`, as was done for thm_7_4 and cor_7_5.

$$
\begin{array}{c} \frac {\partial}{\partial \varepsilon} \bigg | _ {\varepsilon = 0} g _ {\mu \bar {\nu}} (\varepsilon \kappa) = 0, \\ \frac {\partial^ {2}}{\partial \varepsilon \partial \bar {\varepsilon}} \bigg | _ {\varepsilon = 0} g _ {\mu \bar {\nu}} (\varepsilon \kappa) = (\mu \bar {\kappa}, G _ {\Gamma} (\nu \bar {\kappa})) _ {\Gamma} + \left(\mu \bar {\nu}, G _ {\Gamma} (| \kappa | ^ {2})\right) _ {\Gamma}. \end{array}
$$

PROOF. We will use Lemma 8.4 and Theorems 7.4 and 7.7, provided one can interchange $\frac{\partial}{\partial\varepsilon}, \frac{\partial^2}{\partial\varepsilon\partial\varepsilon}$ with the limits. This can be done as in [Ahl62] by showing that limits of corresponding derivatives converge uniformly on $\varepsilon$ in a neighborhood of 0. We omit these standard arguments and concentrate on actual computations.

For the first variation of the Weil-Petersson metric we get

$$
\frac {\partial}{\partial \varepsilon} \bigg | _ {\varepsilon = 0} g _ {\mu \bar {\nu}} (\varepsilon \kappa) = \lim _ {r \to 1 ^ {-}} \lim _ {s \to 1 ^ {-}} \frac {A (\Gamma \backslash \mathbb {D})}{A (\mathbb {D} _ {r})} \left. \frac {\partial}{\partial \varepsilon} \right| _ {\varepsilon = 0} g _ {P (\mu_ {s}) \overline {{P (\nu_ {r})}}} (\varepsilon \kappa).
$$

Since $P(\mu_s), P(\nu_r) \in H^{-1,1}(\mathbb{D})$, we conclude from Theorem 7.4 that this is identically zero.

Similarly, for the second variation we have

$$
\frac {\partial^ {2}}{\partial \varepsilon \partial \bar {\varepsilon}} \bigg | _ {\varepsilon = 0} g _ {\mu \bar {\nu}} (\varepsilon \kappa) = \lim _ {r \to 1 ^ {-}} \lim _ {s \to 1 ^ {-}} \frac {A (\Gamma \backslash \mathbb {D})}{A (\mathbb {D} _ {r})} \left. \frac {\partial^ {2}}{\partial \varepsilon \partial \bar {\varepsilon}} \right| _ {\varepsilon = 0} g _ {P (\mu_ {s}) \overline {{P (\nu_ {r})}}} (\varepsilon \kappa).
$$

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

<!-- page 70 of 136 -->

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

8. FINITE-DIMENSIONAL TEICHMÜLLER SPACES

61

Since $P(\nu_r), P(\mu_s) \in H^{-1,1}(\mathbb{D})$ and $\kappa \in \Omega^{-1,1}(\mathbb{D}, \Gamma) \subset \Omega^{-1,1}(\mathbb{D})$, we get from Theorem 7.7$^6$,

$$
\begin{array}{c} \frac {\partial^ {2}}{\partial \varepsilon \partial \bar {\varepsilon}} \bigg | _ {\varepsilon = 0} g _ {\mu \bar {\nu}} (\varepsilon \kappa) \\ = \lim _ {r \to 1 ^ {-}} \lim _ {s \to 1 ^ {-}} \frac {A (\Gamma \backslash \mathbb {D})}{A (\mathbb {D} _ {r})} \left(\left(P (\mu_ {s}) \bar {\kappa}, G (P (\nu_ {r}) \bar {\kappa})\right) + \left(P (\mu_ {s}) \overline {{P (\nu_ {r})}}, G (| \kappa | ^ {2})\right)\right). \end{array}
$$

By properties RK2 and RK4 in Section 1.4,

$$
\begin{array}{c} \iint_ {\mathbb {D}} | G (P (\nu_ {r}) \kappa) |   | \kappa | \rho (z) d ^ {2} z \leq \| \kappa \| _ {\infty} ^ {2} \iint_ {\mathbb {D}} \iint_ {\mathbb {D}} G (z, w)   | P (\nu_ {r}) (w) |   \rho (z) \rho (w) d ^ {2} w d ^ {2} z \\ = \| \kappa \| _ {\infty} ^ {2} \iint_ {\mathbb {D}} | P (\nu_ {r}) (w) |   \rho (w) d ^ {2} w <   \infty , \end{array}
$$

and by property $\mathbf{RK3}G(|\kappa|^2)$ is bounded on $\mathbb{D}$, so that it follows from Lemma 8.1 that

$$
\left. \frac {\partial^ {2}}{\partial \varepsilon \partial \bar {\varepsilon}} \right| _ {\varepsilon = 0} g _ {\mu \bar {\nu}} (\varepsilon \kappa) = \lim _ {r \rightarrow 1 ^ {-}} \frac {A (\Gamma \backslash \mathbb {D})}{A (\mathbb {D} _ {r})} \left(\left(\mu \bar {\kappa}, G (P (\nu_ {r}) \bar {\kappa})\right) + \left(\mu \overline {{P (\nu_ {r})}}, G (| \kappa | ^ {2})\right)\right).
$$

We have

$$
\begin{array}{c} \left(\mu \bar {\kappa}, G (P (\nu_ {r}) \bar {\kappa})\right) = \iint_ {\mathbb {D} _ {r}} \lambda_ {1} (v) \overline {{\nu (v)}} \rho (v) d ^ {2} v, \\ \left(\mu \overline {{P (\nu_ {r})}}, G (| \kappa | ^ {2})\right) = \iint_ {\mathbb {D} _ {r}} \lambda_ {2} (v) \overline {{\nu (v)}} \rho (v) d ^ {2} v, \end{array}
$$

where

$$
\begin{array}{l} \lambda_ {1} (v) = \frac {1 2}{\pi} \rho (v) ^ {- 1} \iint_ {\mathbb {D}} \iint_ {\mathbb {D}} \frac {\mu (z) \overline {{\kappa (z)}} G (z , u) \kappa (u)}{(1 - u \bar {v}) ^ {4}} \rho (z) d ^ {2} u d ^ {2} z, \\ \lambda_ {2} (v) = \frac {1 2}{\pi} \rho (v) ^ {- 1} \iint_ {\mathbb {D}} \iint_ {\mathbb {D}} \frac {\mu (z) G (z , u) | \kappa (u) | ^ {2}}{(1 - z \bar {v}) ^ {4}} \rho (u) d ^ {2} u d ^ {2} z, \end{array}
$$

and $\lambda_1, \lambda_2 \in \Omega^{-1,1}(\mathbb{D}, \Gamma)$. It follows from Lemma 1.9 that

$$
\begin{array}{l} \frac {\partial^ {2}}{\partial \varepsilon \partial \bar {\varepsilon}} \bigg | _ {\varepsilon = 0} g _ {\mu \bar {\nu}} (\varepsilon \kappa) = \iint_ {\Gamma \backslash \mathbb {D}} \lambda_ {1} (v) \overline {{\nu (v)}} \rho (v) d ^ {2} v + \iint_ {\Gamma \backslash \mathbb {D}} \lambda_ {2} (v) \overline {{\nu (v)}} \rho (v) d ^ {2} v \\ = \frac {1 2}{\pi} \iint_ {\mathbb {D}} \iint_ {\Gamma \backslash \mathbb {D}} \iint_ {\mathbb {D}} \mu (z) \overline {{\kappa (z)}} G (z, u) \kappa (u) \frac {\overline {{\nu (v)}}}{(1 - u \bar {v}) ^ {4}} \rho (z) d ^ {2} u d ^ {2} v d ^ {2} z \\ + \frac {1 2}{\pi} \iint_ {\mathbb {D}} \iint_ {\Gamma \backslash \mathbb {D}} \iint_ {\mathbb {D}} \mu (z) G (z, u) | \kappa (u) | ^ {2} \frac {\overline {{\nu (v)}}}{(1 - z \bar {v}) ^ {4}} \rho (u) d ^ {2} u d ^ {2} v d ^ {2} z \\ = I _ {1} + I _ {2}. \end{array}
$$

<small><span class="docvortex-page-footnote" data-block-type="page_footnote" style="color:#6b7280">$\kappa \in \Omega^{-1,1}(\mathbb{D})$</span></small>

<small><span class="docvortex-page-footnote" data-block-type="page_footnote" style="color:#6b7280">$^{6}$ It is for this case that we need the condition  $\kappa\in\Omega^{-1,1}(\mathbb{D})$  in Theorem 7.7.</span></small>

<!-- page 71 of 136 -->

62

1. CURVATURE PROPERTIES AND CHERN FORMS

As before, the integrals above do not change if we let any one of the integration variables to range over $\Gamma \backslash \mathbb{D}$ while others range over $\mathbb{D}$. We have, using property RK1, (1.7) and (1.20),

$$
\begin{array}{r l} I _ {1} = \frac {1 2}{\pi} \iint_ {\mathbb {D}} \iint_ {\mathbb {D}} \iint_ {\Gamma \backslash \mathbb {D}} \mu (z) \overline {{\kappa (z)}} G (z, u) \kappa (u) \frac {\overline {{\nu (v)}}}{(1 - u \bar {v}) ^ {4}} \rho (z) d ^ {2} u d ^ {2} v d ^ {2} z \\ & = \iint_ {\mathbb {D}} \iint_ {\Gamma \backslash \mathbb {D}} \mu (z) \overline {{\kappa (z)}} G (z, u) \kappa (u) \overline {{\nu (u)}} \rho (u) \rho (z) d ^ {2} u d ^ {2} z \\ & = \iint_ {\Gamma \backslash \mathbb {D}} \iint_ {\Gamma \backslash \mathbb {D}} \mu (z) \overline {{\kappa (z)}} G _ {\Gamma} (z, u) \kappa (u) \overline {{\nu (u)}} \rho (u) \rho (z) d ^ {2} u d ^ {2} z \\ & = (\mu \bar {\kappa}, G _ {\Gamma} (\nu \bar {\kappa})) _ {\Gamma}. \end{array}
$$

Similarly,

$$
\begin{array}{c} I _ {2} = \iint_ {\mathbb {D}} \iint_ {\Gamma \setminus \mathbb {D}} \mu (z) \overline {{\nu (z)}} G (z, u) \left| \kappa (u) \right| ^ {2} \rho (u) \rho (z) d ^ {2} u d ^ {2} z \\ = \iint_ {\Gamma \setminus \mathbb {D}} \iint_ {\Gamma \setminus \mathbb {D}} \mu (z) \overline {{\nu (z)}} G _ {\Gamma} (z, u) \left| \kappa (u) \right| ^ {2} \rho (u) \rho (z) d ^ {2} u d ^ {2} z \\ = \left(\mu \bar {\nu}, G _ {\Gamma} (| \kappa | ^ {2})\right) _ {\Gamma}, \end{array}
$$

and the assertion follows.

REMARK 8.6. Theorem 8.5 was proved by Wolpert [Wol86], and all results on Ricci, sectional, and scalar curvatures for finite-dimensional Teichmüller spaces follow from it.

We conclude this section by deriving a formula for Ricci tensor different from [Wol86], and indicating its application. Let $\mu_1, \ldots, \mu_d$ be an orthonormal basis of $\Omega^{-1,1}(\mathbb{D}, \Gamma)$, which is a subspace of the Hilbert space $L^2(\mathbb{D}, \Gamma)$ of Beltrami differentials $\mu$ for $\Gamma$ such that $|\mu| \in L^2(\Gamma \backslash \mathbb{D}, \rho(z)d^2z)$. Let $P: L^2(\mathbb{D}, \Gamma) \to \Omega^{-1,1}(\mathbb{D}, \Gamma)$ be the orthogonal projector. It follows from the definition and representation (1.7) that $P$ is an integral operator with kernel

$$
P (z, w) = \sum_ {n = 1} ^ {d} \mu_ {n} (z) \overline {{\mu_ {n} (w)}} = \frac {1 2}{\pi} \rho (z) ^ {- 1} \rho (w) ^ {- 1} \sum_ {\gamma \in \Gamma} \frac {\gamma^ {\prime} (w) ^ {2}}{(1 - \bar {z} \gamma (w)) ^ {4}}.
$$

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

<!-- page 72 of 136 -->

8. FINITE-DIMENSIONAL TEICHMÜLLER SPACES

63

The Ricci tensor at the origin of $T(\Gamma)$ is given by

$$
\begin{array}{c}\mathcal{R}_{\mu \bar{\nu}} = \sum_{n = 1}^{d}R_{\mu \bar{\mu}_{n}\mu_{n}\bar{\nu}} = -\sum_{n = 1}^{d}\left(\left(\mu \bar{\nu},G_{\Gamma}(|\mu_{n}|^{2})\right)_{\Gamma} + (\mu \bar{\mu}_{n},G_{\Gamma}(\nu \bar{\mu}_{n}))_{\Gamma}\right)\\= -\sum_{n = 1}^{d}\left(\iint \limits_{\Gamma \setminus \mathbb{D}}\iint \limits_{\Gamma \setminus \mathbb{D}}\mu (z)\overline{\nu(z)} G_{\Gamma}(z,w)|\mu_{n}(w)|^{2}\rho (w)\rho (z)d^{2}wd^{2}z\right.\\+\iint \limits_{\Gamma \setminus \mathbb{D}}\iint \limits_{\Gamma \setminus \mathbb{D}}\mu (z)\overline{\mu_{n}(z)} G_{\Gamma}(z,w)\mu_{n}(w)\overline{\nu(w)} \rho (w)\rho (z)d^{2}wd^{2}z\left. \right)\\= -\frac{12}{\pi}\iint \limits_{\mathbb{D}}\iint \limits_{\Gamma \setminus \mathbb{D}}\mu (z)\overline{\nu(z)} G(z,w)\sum_{\gamma \in \Gamma}\frac{\gamma^{\prime}(w)^{2}}{(1 - \bar{w}\gamma(w))^{4}}\rho (w)^{-1}\rho (z)d^{2}wd^{2}z\\-\frac{12}{\pi}\iint \limits_{\Gamma \setminus \mathbb{D}}\iint \limits_{\mathbb{D}}\mu (z)\overline{\nu(w)} G(z,w)\sum_{\gamma \in \Gamma}\frac{\gamma^{\prime}(z)^{2}}{(1 - \bar{w}\gamma(z))^{4}}d^{2}wd^{2}z,\end{array}\tag{8.1}
$$

where nothing is changed if we let any of the integration variables to range over $\Gamma \backslash \mathbb{D}$ while other range over $\mathbb{D}$.

It is instructive to compare the Ricci curvatures of the finite-dimensional Teichmüller space $T(\Gamma)$ and that of the universal Teichmüller space $T(1)$.

First, $T(\Gamma)$ is no longer a Kähler-Einstein manifold. Second, the sum over $\Gamma$ in (8.1) can be transformed into a sum over the conjugacy classes of $\Gamma$. As is in [TZ91], using variational formulas for the Selberg zeta-function, we find that the contribution of the hyperbolic conjugacy classes is the second variation of the Selberg zeta-function at $s = 2$. The contribution of parabolic conjugacy classes (if they are present) yields a new Kähler metric on $T(\Gamma)$, introduced in [TZ91]. The contribution of the identity element, as it follows from Theorem 7.11, is

$$
\begin{array}{c} - \frac {3}{4 \pi} \iint_ {\mathbb {D}} \iint_ {\Gamma \backslash \mathbb {D}} \mu (z) \overline {{\nu (z)}} G (z, w) \rho (w) \rho (z) d ^ {2} w d ^ {2} z \\ - \frac {1 2}{\pi} \iint_ {\Gamma \backslash \mathbb {D}} \iint_ {\mathbb {D}} \mu (z) \overline {{\nu (w)}} G (z, w) \frac {1}{(1 - z \bar {w}) ^ {4}} d ^ {2} w d ^ {2} z = - \frac {1 3}{1 2 \pi} (\mu , \nu) _ {\Gamma}. \end{array}
$$

As a result, we obtain a local index theorem for families of  $\bar{\partial}$ -operators acting on quadratic differentials on Riemann surfaces, proved in [TZ91]. The above arguments interpret it as an “averaged form” of Theorem 7.11. Detailed derivation of the local index theorem for families from (8.1) will be presented elsewhere.

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

<!-- page 73 of 136 -->

This page intentionally left blank

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

<!-- page 74 of 136 -->

## CHAPTER 2

## Kähler Potential and Period Mapping

## 1. Hilbert spaces and univalent functions

It is well-known (see, e.g., Section 1.2 in Chapter I) that the universal Teichmüller space $T(1)$ is isomorphic to the space $\mathcal{D}$ of univalent functions on $\mathbb{D}$. Here we characterize the univalent functions associated with the Hilbert manifold $T_0(1)$.

In addition to the Hilbert spaces $A_2(\mathbb{D})$ and $A_2(\mathbb{D}^*)$, introduced in Section 2 in Chapter 1, we define the following Hilbert spaces of holomorphic functions,

$$
\begin{array}{c} A _ {2} ^ {1} (\mathbb {D}) = \left\{\psi \text {holomorphic on} \mathbb {D}: \| \psi \| _ {2} ^ {2} = \iint_ {\mathbb {D}} | \psi (z) | ^ {2} d ^ {2} z <   \infty \right\}, \\ A _ {2} ^ {1} (\mathbb {D} ^ {*}) = \left\{\psi \text {holomorphic on} \mathbb {D} ^ {*}: \| \psi \| _ {2} ^ {2} = \iint_ {\mathbb {D} ^ {*}} | \psi (z) | ^ {2} d ^ {2} z <   \infty \right\}. \end{array}
$$

We denote by $\overline{A_2^1(\mathbb{D})}$ and $\overline{A_2^1(\mathbb{D}^*)}$ the corresponding Hilbert spaces of antiholomorphic functions.

REMARK 1.1. Every $\psi \in A_2^1(\mathbb{D})$ corresponds to a holomorphic 1-form $\omega = \psi(z)dz$ on $\mathbb{D}$ (or on $\Gamma \backslash \mathbb{D}$ for a cofinite Fuchsian group $\Gamma$) such that the (1,1)-form $\omega \wedge \bar{\omega}$ is integrable. Similarly, every $\phi \in A_2(\mathbb{D})$ corresponds to a holomorphic quadratic differential $q = \phi(z)(dz)^2$ on $\mathbb{D}$ (or on $\Gamma \backslash \mathbb{D}$) such that the (1,1)-form $(|\phi(z)|^2 / \rho(z))dz \wedge d\bar{z}$ is integrable, so that the latter space could be also denoted by $A_2^2(\mathbb{D})$. We will use the same notation $\| \|_2$ for the norms in these Hilbert spaces. To avoid confusion, in the main text we always denote elements in the spaces $A_2$ by $\phi$, and elements in the spaces $A_2^1$ by $\psi$.

In addition to the Banach spaces $A_{\infty}(\mathbb{D})$ and $A_{\infty}(\mathbb{D}^{*})$ introduced in Section 1.1 of Chapter 1, we define the following Banach spaces of holomorphic functions,

$$
A _ {\infty} ^ {1} (\mathbb {D}) = \left\{\psi \text {holomorphic on} \mathbb {D}: \| \psi \| _ {\infty} = \sup _ {z \in \mathbb {D}} \big | (1 - | z | ^ {2}) \psi (z) \big | <   \infty \right\},
$$

$$
A _ {\infty} ^ {1} (\mathbb {D} ^ {*}) = \left\{\psi \text {holomorphic on} \mathbb {D} ^ {*}: \| \psi \| _ {\infty} = \sup _ {z \in \mathbb {D} ^ {*}} \big | (1 - | z | ^ {2}) \psi (z) \big | <   \infty \right\}.
$$

For a holomorphic function $f:\Omega \to \mathbb{C}$ such that $f^{\prime}\neq 0$ on $\Omega$ we set

$$
\mathcal {A} (f) = \frac {f ^ {\prime \prime}}{f ^ {\prime}}.
$$

REMARK 1.2. Classical distortion theorem (see e.g., [Pom92, Dur83]) implies that if $f:\mathbb{D}\to\mathbb{C}$ and $g:\mathbb{D}^{*}\to\mathbb{C}$ are univalent functions, then $\mathcal{A}(f)\in A_{\infty}^{1}(\mathbb{D})$ and


> **[IMPLICIT HYPOTHESIS 4-03]** (TT:3520; Lean: `remark_1_2` clause 2 (distortion, exterior), Ch2/S1_Completed) Implicit normalization. For g = 1/z, 𝒜(g) = −2/z ∉ A∞¹(𝔻*).

65

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

<!-- page 75 of 136 -->

66

2. KÄHLER POTENTIAL AND PERIOD MAPPING

$\mathcal{A}(g)\in A_{\infty}^{1}(\mathbb{D}^{*})$ . In [Teo04], it was shown that the Bers embedding of the universal Teichmüller curve $\mathcal{T}(1)$ into $A_{\infty}(\mathbb{D})\oplus \mathbb{C}$ can be factorized as the composition of two holomorphic embeddings

$$
\mathcal {T} (1) \to A _ {\infty} ^ {1} (\mathbb {D}) \to A _ {\infty} (\mathbb {D}) \oplus \mathbb {C}.
$$

Here the map $\mathcal{T}(1)\to A_{\infty}^{1}(\mathbb{D})$ is given by $\gamma = g^{-1}\circ f\mapsto \mathcal{A}(f)$ and the map $A_{\infty}^{1}(\mathbb{D})\to A_{\infty}(\mathbb{D})\oplus \mathbb{C}$ is defined as

$$
\psi \mapsto \left(\psi_ {z} - \frac {1}{2} \psi^ {2}, \frac {1}{2} \psi (0)\right).
$$

Similar to Lemma 2.1 in Chapter 1, we have

LEMMA 1.3. The vector spaces $A_2^1(\mathbb{D})$ and $A_2^1(\mathbb{D}^*)$ are subspaces of $A_{\infty}^{1}(\mathbb{D})$ and $A_{\infty}^{1}(\mathbb{D}^{*})$ respectively. The natural inclusion maps $A_2^1(\mathbb{D}) \hookrightarrow A_{\infty}^{1}(\mathbb{D})$ and $A_2^1(\mathbb{D}^*) \hookrightarrow A_{\infty}^{1}(\mathbb{D}^{*})$ are bounded linear mappings of Banach spaces.

PROOF. It is sufficient to consider only the spaces of holomorphic functions on $\mathbb{D}$. For every $\psi \in A_2^1 (\mathbb{D})$ let $\psi (z) = \sum_{n = 1}^{\infty}na_nz^{n - 1}$ be the power series expansion. Then

$$
\| \psi \| _ {2} ^ {2} = \iint_ {\mathbb {D}} | \psi (z) | ^ {2} d ^ {2} z = \pi \sum_ {n = 1} ^ {\infty} n | a _ {n} | ^ {2},
$$

and by Cauchy-Schwarz inequality, we have

$$
| \psi (z) | \leq \sum_ {n = 1} ^ {\infty} n | a _ {n} | | z | ^ {n - 1} \leq \left(\sum_ {n = 1} ^ {\infty} n | a _ {n} | ^ {2}\right) ^ {1 / 2} \left(\sum_ {n = 1} ^ {\infty} n | z | ^ {2 n - 2}\right) ^ {1 / 2}
$$

for every $z\in \mathbb{D}$ . Using

$$
\sum_ {n = 1} ^ {\infty} n | z | ^ {2 n - 2} = \frac {1}{(1 - | z | ^ {2}) ^ {2}},
$$

we get

$$
\| \psi \| _ {\infty} = \sup _ {z \in \mathbb {D}} | (1 - | z | ^ {2}) \psi (z) | \leq \frac {1}{\sqrt {\pi}} \| \psi \| _ {2}.
$$

Similar to Remark 2.2 in Chapter 1, we get

COROLLARY 1.4. For every $\psi \in A_2^1 (\mathbb{D})$,

$$
\lim _ {| z | \to 1 ^ {-}} (1 - | z | ^ {2}) \psi (z) = 0.
$$

Similar statement holds for every $\psi \in A_2^1 (\mathbb{D}^*)$.

For a holomorphic function $f:\Omega \to \mathbb{C}$ set

$$
\Psi (f) = f _ {z} - \frac {1}{2} f ^ {2}.
$$

If $f' \neq 0$ on $\Omega$, then $\mathcal{S}(f) = (\Psi \circ \mathcal{A})(f)$, where $\mathcal{S}(f)$ is the Schwarzian derivative of $f$. In [Teo04] it was proved that $\Psi\left(A_{\infty}^{1}(\mathbb{D})\right) \subset A_{\infty}(\mathbb{D})$ and $\Psi\left(A_{\infty}^{1}(\mathbb{D}^{*})\right) \subset A_{\infty}(\mathbb{D}^{*})$. Similarly, we have the following result.


> **[ERRATUM 4-02]** (TT:3588 (citing [Teo04]); Lean: `remark_1_2` clause 4 (Ψ exterior), Ch2/S1_Completed) False for ψ = z⁻² (lean4 `PsiExteriorDiagnostic`). Same defect as 4-01, inherited from arXiv math/0406408 Lemma 2.5. Correct version: add cubic decay; the normalized 𝒜(g), g = bz + b₀ + O(1/z), satisfies it.

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026for download from IP 130.34.46.51.

LEMMA 1.5. $\Psi\left(A_{2}^{1}(\mathbb{D})\right)\subset A_{2}(\mathbb{D})$ and $\Psi\left(A_{2}^{1}(\mathbb{D}^{*})\right)\subset A_{2}(\mathbb{D}^{*}).$


> **[ERRATUM 4-01]** (TT:3592–3600; Lean: `lemma_1_5`, Ch2/S1_UnivalentFunctions) The exterior claim is false. For ψ = z⁻² ∈ A₂¹(𝔻*), Ψ(ψ) ∉ A₂(𝔻*) (`psiOp_not_mem_A2`). The reduction to 𝔻 by inversion fails: the inversion law for Ψ has an extra term (`PsiOp_inversion_identity`, "plus sign"), harmless only under cubic decay. Correct version: restrict to Ã₂¹(𝔻*) (decay O(z⁻³), as TT itself does at TT:5942).

<!-- page 76 of 136 -->

1. HILBERT SPACES AND UNIVALENT FUNCTIONS

67

PROOF. It is sufficient to consider functions on $\mathbb{D}$. For $\psi = \sum_{n=1}^{\infty} na_n z^{n-1} \in A_2^1(\mathbb{D})$ we have

$$
\iint_ {\mathbb {D}} | \Psi (\psi) | ^ {2} \rho (z) ^ {- 1} d ^ {2} z \leq 2 \iint_ {\mathbb {D}} | \psi_ {z} (z) | ^ {2} \rho (z) ^ {- 1} d ^ {2} z + \frac {1}{2} \iint_ {\mathbb {D}} | \psi (z) | ^ {4} \rho (z) ^ {- 1} d ^ {2} z.
$$

For the first term, a straightforward computation gives

$$
\iint_ {\mathbb {D}} | \psi_ {z} (z) | ^ {2} \rho (z) ^ {- 1} d ^ {2} z = \frac {\pi}{2} \sum_ {n = 2} ^ {\infty} \frac {n (n - 1)}{n + 1} | a _ {n} | ^ {2} <   \frac {1}{2} \| \psi \| _ {2} ^ {2} <   \infty .
$$

For the second term, since $\psi \in A_{\infty}^{1}(\mathbb{D})$, we have

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026for download from IP 130.34.46.51.

$$
\iint_ {\mathbb {D}} \rho (z) ^ {- 1} | \psi (z) | ^ {4} d ^ {2} z \leq \frac {1}{4} \| \psi \| _ {\infty} ^ {2} \| \psi \| _ {2} ^ {2} <   \infty .
$$

The following theorem of Becker and Pommerenke [BP78] characterizes univalent functions on $\mathbb{D}$ that admit a q.c. extension to a larger domain such that the complex dilation is continuous on $S^1$.

THEOREM 1.6. Let $f: \mathbb{D} \to \mathbb{C}$ be a univalent function such that $f(\mathbb{D})$ is a Jordan domain. Then the following conditions are equivalent.


> **[IMPLICIT HYPOTHESIS 4-04]** (TT:3622–3638; Lean: `thm_1_6` (Becker–Pommerenke), Ch2/S1_BP16Completed) "Jordan domain" is meant in ℂ (bounded). For f = 1/(1−z), a half-plane bounded by a line through ∞, (ii) ⇒ (iii) fails.

(i) $f$ has a q.c. extension $F$ to $\{z: |z| < R, R > 1\}$ such that the complex dilation $\mu(z) = F_{\bar{z}} / F_z$ satisfies

$$
\lim _ {| z | \to 1 ^ {+}} \mu (z) = 0.
$$

(ii)

$$
\lim _ {| z | \to 1 ^ {-}} (1 - | z | ^ {2}) ^ {2} \mathcal {S} (f) (z) = 0.\tag{iii}
$$

$$
\lim _ {| z | \to 1 ^ {-}} (1 - | z | ^ {2}) \mathcal {A} (f) (z) = 0.
$$

In [GS92], Gardiner and Sullivan have studied the subgroup

$$
S = \operatorname{Möb} (S ^ {1}) \backslash \operatorname{Homeo} _ {s} (S ^ {1})
$$

of symmetric homeomorphisms in $QS = \mathrm{Möb}(S^1) \backslash \mathrm{Homeo}_{qs}(S^1) \simeq T(1)$. They proved that as a Banach submanifold of $T(1)$, $S$ is a topological group, and that univalent functions $f$ associated to elements in $S$ are precisely the functions satisfying condition (ii) of Theorem 1.6.

REMARK 1.7. Actually in [GS92] this condition is stated as follows: for every $\varepsilon > 0$ there is a compact subset $K$ of $\mathbb{D}$ such that $|(1 - |z|^2)^2\mathcal{S}(f)(z)| < \varepsilon$ for $z \in \mathbb{D} \setminus K$, which is clearly equivalent to (ii).

Using this remark and Remark 2.2 in Chapter 1, we get the following statement.

COROLLARY 1.8. The group $T_0(1)$ is a subgroup of $S$.

<!-- page 77 of 136 -->

68

2. KÄHLER POTENTIAL AND PERIOD MAPPING

REMARK 1.9. It is known [GS92] that the topological group $S$ contains the subgroup of $C^1$-homeomorphisms of $S^1$. Similarly, the topological group $T_0(1)$ contains the subgroup of $C^3$-homeomorphisms. Indeed, it is known (see, e.g., [Ham02]) that if $\gamma \in QS$ is $C^3$ then corresponding $f$ and $g$ are of $C^2$ class on the boundary and all their derivatives are Holder continuous with $\alpha < 1$. From here it follows that $S(f) \in A_2(\mathbb{D})$.

REMARK 1.10. For $[\mu] \in T_0(1)$ it is an interesting open problem to characterize intrinsically the corresponding map $w_\mu|_{S^1}$ and the quasi-circle f($S^1$), as it was done for by Gardiner and Sullivan in [GS92] for $[\mu] \in S$.

Another important consequence of Becker-Pommerenke Theorem is the following result.

LEMMA 1.11. Let $f$ and $g$ be univalent functions on $\mathbb{D}$ and $\mathbb{D}^*$ such that $S(f) \in A_2(\mathbb{D})$ and $S(g) \in A_2(\mathbb{D}^*)$. Then $\mathcal{A}(f) \in A_2^1(\mathbb{D})$ and $\mathcal{A}(g) \in A_2^1(\mathbb{D}^*)$.


> **[ERRATUM 4-05]** (TT:3666–3734; Lean: `lemma_1_11`, Ch2/S1_T112Completed) False as stated: f = z/(1−z) has 𝒮(f) = 0 but 𝒜(f) ∉ A₂¹(𝔻) (lean4 `Lemma111DiskDiagnostic`). The proof applies Thm 1.6, which needs the Jordan hypotheses. They hold for welding pairs, so Thm 1.12 is unaffected. Correct version: the statement with these hypotheses.

PROOF. It is sufficient to consider functions on $\mathbb{D}$. If $S(f) \in A_2(\mathbb{D})$, then by Remark 2.2 in Chapter 1 $f$ satisfies the condition (ii) in Theorem 1.6 and hence it satisfies the condition (iii). In particular, there exists $r' > 0$ such that

$$
(1 - | z | ^ {2}) | \mathcal {A} (f) (z) | \leq 1 / 2 \quad \text {for all} \quad r ^ {\prime} <   | z | <   1.
$$

By triangle and geometric mean inequalities,

$$
\begin{array}{r l} & {| \mathcal {S} (f) (z) | ^ {2} \geq \left(| \mathcal {A} (f) ^ {\prime} (z) | - \frac {1}{2} | \mathcal {A} (f) (z) | ^ {2}\right) ^ {2}} \\ & {\qquad = | \mathcal {A} (f) ^ {\prime} (z) | ^ {2} + \frac {1}{4} | \mathcal {A} (f) (z) | ^ {4} - | \mathcal {A} (f) ^ {\prime} (z) | | \mathcal {A} (f) (z) | ^ {2}} \\ & {\qquad \geq \frac {1}{2} \left(| \mathcal {A} (f) ^ {\prime} (z) | ^ {2} - | \mathcal {A} (f) (z) | ^ {4}\right),} \end{array}
$$

so that for $r' < |z| < 1$,

$$
2 (1 - | z | ^ {2}) ^ {2} | \mathcal {S} (f) (z) | ^ {2} \geq (1 - | z | ^ {2}) ^ {2} | \mathcal {A} (f) ^ {\prime} (z) | ^ {2} - \frac {1}{4} | \mathcal {A} (f) (z) | ^ {2}.\tag{1.1}
$$

Let $\mathcal{A}(f)(z) = \sum_{n=1}^{\infty} na_n z^{n-1}$ be the power series expansion of $\mathcal{A}(f)$ and let $\mathbb{D}_r$ be the disk of radius $r$. We have,

$$
\iint_ {\mathbb {D} _ {r}} (1 - | z | ^ {2}) ^ {2} | \mathcal {A} (f) ^ {\prime} (z) | ^ {2} d ^ {2} z = \pi \sum_ {n = 2} ^ {\infty} n ^ {2} (n - 1) ^ {2} | a _ {n} | ^ {2} r ^ {2 n} \left(\frac {r ^ {- 2}}{n - 1} - \frac {2}{n} + \frac {r ^ {2}}{n + 1}\right)
$$

and

$$
\iint_ {\mathbb {D} _ {r}} | \mathcal {A} (f) (z) | ^ {2} d ^ {2} z = \pi \sum_ {n = 1} ^ {\infty} n | a _ {n} | ^ {2} r ^ {2 n}.
$$

Using the elementary inequality

$$
(n - 1) ^ {2} \left(\frac {r ^ {- 2}}{n - 1} - \frac {2}{n} + \frac {r ^ {2}}{n + 1}\right) \geq \frac {1}{2 n}
$$

for all $n \geq 2$ and $0 < r < 1$, we get

(1.2)

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

$$
\iint_ {\mathbb {D} _ {r}} (1 - | z | ^ {2}) ^ {2} | \mathcal {A} (f) ^ {\prime} (z) | ^ {2} d ^ {2} z \geq \frac {1}{2} \iint_ {\mathbb {D} _ {r}} | \mathcal {A} (f) (z) | ^ {2} d ^ {2} z - \frac {\pi}{2} | a _ {1} | ^ {2} r ^ {2}.
$$

<!-- page 78 of 136 -->

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026for download from IP 130.34.46.51.

1. HILBERT SPACES AND UNIVALENT FUNCTIONS

69

Integrating the inequality (1.1) over $\mathbb{D}_r\setminus \mathbb{D}_{r'}$, and using (1.2), we get for $r > r'$,

$$
\left| \begin{array}{c} 2 \iint_ {\mathbb {D} _ {r} \setminus \mathbb {D} _ {r ^ {\prime}}} (1 - | z | ^ {2}) ^ {2} | \mathcal {S} (f) (z) | ^ {2} d ^ {2} z \geq \iint_ {\mathbb {D} _ {r} \setminus \mathbb {D} _ {r ^ {\prime}}} \big ((1 - | z | ^ {2}) ^ {2} | \mathcal {A} (f) ^ {\prime} (z) | ^ {2} - \frac {1}{4} | \mathcal {A} (f) (z) | ^ {2} \big)   d ^ {2} z \\ = \iint_ {\mathbb {D} _ {r}} (1 - | z | ^ {2}) ^ {2} | \mathcal {A} (f) ^ {\prime} (z) | ^ {2} d ^ {2} z - \frac {1}{4} \iint_ {\mathbb {D} _ {r}} | \mathcal {A} (f) (z) | ^ {2} d ^ {2} z \\ - \iint_ {\mathbb {D} _ {r ^ {\prime}}} (1 - | z | ^ {2}) ^ {2} | \mathcal {A} (f) ^ {\prime} (z) | ^ {2} d ^ {2} z + \frac {1}{4} \iint_ {\mathbb {D} _ {r ^ {\prime}}} | \mathcal {A} (f) (z) | ^ {2} d ^ {2} z \\ \geq \frac {1}{4} \iint_ {\mathbb {D} _ {r}} | \mathcal {A} (f) (z) | ^ {2} d ^ {2} z + \frac {1}{4} \iint_ {\mathbb {D} _ {r ^ {\prime}}} | \mathcal {A} (f) (z) | ^ {2} d ^ {2} z \\ - \iint_ {\mathbb {D} _ {r ^ {\prime}}} (1 - | z | ^ {2}) ^ {2} | \mathcal {A} (f) ^ {\prime} (z) | ^ {2} d ^ {2} z - \frac {\pi}{2} | a _ {1} | ^ {2} r ^ {2}. \end{array} \right|
$$

Since $S(f) \in A_2(\mathbb{D})$, from this inequality we conclude that there exists $C > 0$ such that

$$
\left| \iint_ {\mathbb {D} _ {r}} | \mathcal {A} (f) (z) | ^ {2} d ^ {2} z <   C \right|
$$

for all $0 < r < 1$, i.e., $\mathcal{A}(f) \in A_2^1(\mathbb{D})$.

The following statement is the main result of this section.

THEOREM 1.12. Let $w_{\mu} = \mathrm{g}_{\mu}^{-1} \circ \mathrm{f}^{\mu}$ be the conformal welding corresponding to $[\mu] \in T(1)$. Then $[\mu] \in T_0(1)$ if and only if one of the following conditions holds.

(i) $\mathcal{S}(\mathrm{f}^{\mu})\in A_{2}(\mathbb{D})$

(ii) $\mathcal{A}(\mathrm{f}^{\mu})\in A_{3}^{1}(\mathbb{D})$


> **[ERRATUM 4-07]** (TT:3742; Lean: `thm_1_12` (ii), Ch2/S1_UnivalentFunctions (module note)) OCR error in the source text; (iv) and Lemma 1.11 read A₂¹.

(iii)  $\mathcal{S}(g_{\mu}) \in A_{2}(\mathbb{D}^{*})$

(iv) $\mathcal{A}(\mathbf{g}_{\mu})\in A_{2}^{1}(\mathbb{D}^{\star})$

PROOF. Since under the Bers embedding $\beta(T_0(1)) = \beta(T(1)) \cap A_2(\mathbb{D})$, it follows that if $w_\mu = \mathrm{g}_\mu^{-1} \circ \mathrm{f}^\mu$ is the conformal welding associated to $[\mu] \in T(1)$, then $\mathcal{S}(\mathrm{f}^\mu) \in A_2(\mathbb{D})$ if and only if $[\mu] \in T_0(1)$. Let $j$ be the antiholomorphic inversion $z \mapsto 1/\bar{z}$. Since q.c. mapping $w_\mu$ on $\hat{\mathbb{C}}$ satisfies $j \circ w_\mu \circ j = w_\mu$, we have

$$
w _ {\mu} ^ {- 1} = j \circ w _ {\mu} ^ {- 1} \circ j = (j \circ (\mathrm{f} ^ {\mu}) ^ {- 1} \circ j) \circ (j \circ \mathrm{g} _ {\mu} \circ j).
$$

Thus

$$
\mathrm{f} ^ {\mu^ {- 1}} = r \circ j \circ \mathrm{g} _ {\mu} \circ j \quad \text {and} \quad \mathrm{g} _ {\mu^ {- 1}} = r \circ j \circ \mathrm{f} ^ {\mu} \circ j,\tag{1.3}
$$

where $r$ is the dilation $z \mapsto \overline{g_{\mu}^{\prime}(\infty)} z$. Since $[\mu^{-1}] \in T_0(1)$ if and only $[\mu] \in T_0(1)$, we have $\mathcal{S}(\mathrm{f}^{\mu}) \in A_2(\mathbb{D})$ if and only if $\mathcal{S}(\mathrm{f}^{\mu^{-1}}) \in A_2(\mathbb{D})$, and hence if and only if

$$
\mathcal {S} (\mathrm{g} _ {\mu}) = \overline {{\mathcal {S} (\mathrm{f} ^ {\mu - 1}) \circ j   j _ {\bar {z}} ^ {2}}} \in A _ {2} (\mathbb {D} ^ {*}).
$$

The statement of the theorem now follows from Lemmas 1.5 and 1.11.

Let $\mathcal{T}_0(1)$ be the Teichmüller curve of $T_0(1)$, i.e., the inverse image of $T_0(1)$ under the fibration $\mathcal{T}(1) \to T(1)$ of Hilbert manifolds. It was proved in Section 3 in Chapter 1 that $\mathcal{T}_0(1)$ is a topological group. Using proofs of Lemma 1.5 and Theorem 1.11, we can easily modify the proof in the Appendix of [Teo04] to show

<!-- page 79 of 136 -->

70

2. KÄHLER POTENTIAL AND PERIOD MAPPING

that $A_2^1 (\mathbb{D})$ and $A_{2}(\mathbb{D})\oplus \mathbb{C}$ induce the same Hilbert manifold structure on $\mathcal{T}_0(1)$. We leave the details to Appendix A.

Results of this section justify the following

DEFINITION 1.13. The “universal Liouville action”  $S_{1}: T_{0}(1) \to \mathbb{R}$  is defined by

$$
\mathsf {S} _ {1} ([ \mu ]) = \iint_ {\mathbb {D}} | \mathcal {A} (\mathrm{f} ^ {\mu}) | ^ {2} d ^ {2} z + \iint_ {\mathbb {D} ^ {*}} | \mathcal {A} (\mathrm{g} _ {\mu}) | ^ {2} d ^ {2} z - 4 \pi \log | \mathrm{g} _ {\mu} ^ {\prime} (\infty) |,
$$

where $w_{\mu} = \mathrm{g}_{\mu}^{-1}\circ \mathrm{f}^{\mu}$ is the conformal welding corresponding to $[\mu ]\in T_0(1)$.

We will prove in Section 5 that the universal Liouville action is a Kähler potential of the Weil-Petersson metric on $T_0(1)$.

REMARK 1.14. When $\mathrm{g}_{\mu}^{\prime}$ is continuous on $S^1$, the last term in the definition of $S_{1}$ can be written as


> **[IMPLICIT HYPOTHESIS 4-08]** (TT:3790–3796; Lean: `remark_1_14`, Ch2/S1_Part4) The mean-value passage r → 1 needs log\|h\| regular on S¹. With zeros on S¹ a singular inner factor may intervene; I could not decide whether the unrestricted claim is true.

$$
- 2 \oint_ {S ^ {1}} \log | g _ {\mu} ^ {\prime} (e ^ {i \theta}) | d \theta .
$$

When the quasicircle $\mathrm{g}_{\mu}(S^1) = \mathrm{f}^{\mu}(S^1)$ is of $C^3$ class, functionals of this type were studied by Schiffer and Hawley in [SH62]. Here we extend the definition to quasicirles for the Hilbert manifold $T_0(1)$.

## 2. Grunsky operators for $T_0(1)$

2.1. Grunsky coefficients and operators. Here we prove that Grunsky operators associated to a point in $T_0(1)$ are Hilbert-Schmidt. Suppose that $f: \mathbb{D} \to \mathbb{C}$ and $g: \mathbb{D}^* \to \mathbb{C}$ are univalent functions on $\mathbb{D}$ and $\mathbb{D}^*$ such that $f(0) = 0$, $f'(0) = 1$, $g(\infty) = \infty$, and $f(\mathbb{D}) \cap g(\mathbb{D}^*) = \emptyset$. Such univalent functions are said to form a normalized disjoint pair. The generalized Grunsky coefficients $b_{n,m}, n, m \in \mathbb{Z}$ of a normalized disjoint pair $(f, g)$ are defined as follows (see e.g., [Pom92])

$$
\log \frac {g (z) - g (\zeta)}{z - \zeta} = b _ {0 0} - \sum_ {m = 1} ^ {\infty} \sum_ {n = 1} ^ {\infty} b _ {m n} z ^ {- m} \zeta^ {- n},
$$

$$
\left| \log \frac {g (z) - f (\zeta)}{b z} = - \sum_ {m = 1} ^ {\infty} \sum_ {n = 0} ^ {\infty} b _ {m, - n} z ^ {- m} \zeta^ {n}, \right.
$$

$$
\log \frac {f (z) - f (\zeta)}{z - \zeta} = b _ {0 0} - \sum_ {m = 0} ^ {\infty} \sum_ {n = 0} ^ {\infty} b _ {- m, - n} z ^ {m} \zeta^ {n}.
$$

By definition, $b_{00} = \log b$, where $b = g'(\infty)$. Grunsky coefficients $b_{n,m}$ are symmetric in $n, m$ when $n, m \geq 1$ or $n, m \leq 0$, so for $n \geq 0, m \geq 1$, we define $b_{-n,m} = b_{m,-n}$. It is also clear that coefficients $b_{n,m}$, $|n| \geq 1$ and $|m| \geq 1$ do not changed when $f$ and $g$ are simultaneously post-composed with a dilation $z \mapsto rz$.

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026for download from IP 130.34.46.51.

Grunsky coefficients satisfy the generalized Grunsky inequality, due to Hummel [Hum72] (see also [Pom92]).

THEOREM 2.1. Let $(f,g)$ be a normalized disjoint pair of univalent functions. Then for every $\lambda_{-m},\ldots ,\lambda_m\in \mathbb{C}$,

$$
\sum_ {k = - \infty} ^ {\infty} | k | \left| \sum_ {l = - m} ^ {m} b _ {k l} \lambda_ {l} \right| ^ {2} \leq \sum_ {k = - m} ^ {m ^ {\prime}} \frac {| \lambda_ {k} | ^ {2}}{| k |} + 2 \operatorname{Re} \left[ \bar {\lambda} _ {0} \sum_ {l = - m} ^ {m} b _ {0 l} \lambda_ {l} \right],
$$

<!-- page 80 of 136 -->

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026for download from IP 130.34.46.51.

2. GRUNSKY OPERATORS FOR $T_0(1)$

71

where the prime over the sum indicates that the term $k = 0$ is omitted. The equality for all $\lambda_{-m},\ldots ,\lambda_m$ holds if and only if the set $F = \mathbb{C}\backslash \{f(\mathbb{D})\cup g(\mathbb{D}^{*})\}$ has Lebesgue measure zero.

REMARK 2.2. For $\gamma \in \mathcal{T}(1)$ let $\gamma = g^{-1} \circ f$ be the corresponding conformal welding. Since $(f, g)$ is a normalized disjoint pair of univalent functions and the quasicircle $\mathcal{C} = f(S^1) = g(S^1)$ has Lebesgue measure zero, corresponding Grunsky coefficients $b_{mn}$ satisfy the generalized Grunsky equality. Setting $\lambda_0 = 1$ and $\lambda_k = 0, k \neq 0$, we get

$$
2 \operatorname{Re} b _ {0 0} = \sum_ {k = - \infty} ^ {\infty} | k | | b _ {k 0} | ^ {2}.
$$

Since

$$
\log \frac {g (z)}{z} = b _ {0 0} - \sum_ {k = 1} ^ {\infty} b _ {k 0} z ^ {- k}, \quad \text {and} \quad \log \frac {f (z)}{z} = - \sum_ {k = 1} ^ {\infty} b _ {- k, 0} z ^ {k},
$$

and $\mathrm{Re}b_{00} = \log |g'(\infty)|$, we have

$$
2 \pi \log | g ^ {\prime} (\infty) | = \iint_ {\mathbb {D}} \left| \frac {f ^ {\prime} (z)}{f (z)} - \frac {1}{z} \right| ^ {2} d ^ {2} z + \iint_ {\mathbb {D} ^ {*}} \left| \frac {g ^ {\prime} (z)}{g (z)} - \frac {1}{z} \right| ^ {2} d ^ {2} z.
$$

According to Theorem 4.3 in Chapter 1, this gives an integral formula for the Kähler potential of the Velling-Kirillov metric on $\mathcal{T}(1)$.

Now let $(f,g)$ be a normalized disjoint pair of univalent functions such that the corresponding set $F$ has Lebesgue measure zero. Putting in the generalized Grunsky equality $\lambda_0 = 0$ and rescaling $\lambda_l \mapsto \sqrt{|l|}\lambda_l$, we obtain the following equality

$$
\sum_ {k = - \infty} ^ {\infty} \left| \sum_ {l = - m} ^ {m ^ {'}} \sqrt {| k l |} b _ {k l} \lambda_ {l} \right| ^ {2} = \sum_ {k = - m} ^ {m ^ {'}} | \lambda_ {k} | ^ {2}.
$$

By polarization, we get

$$
\sum_ {k = - \infty} ^ {\infty} ^ {\prime} \sum_ {l = - m} ^ {m} ^ {\prime} \sum_ {l ^ {\prime} = - m} ^ {m} ^ {\prime} \sqrt {| k l |} b _ {k l} \sqrt {| k l ^ {\prime} |} \overline {{b _ {k l ^ {\prime}}}} \lambda_ {l} \bar {\eta} _ {l ^ {\prime}} = \sum_ {k = - m} ^ {m} ^ {\prime} \lambda_ {k} \bar {\eta} _ {k},\tag{2.1}
$$

where $\lambda_{k},\eta_{k}$ are arbitrary complex numbers. Grunsky coefficients $b_{mn}$ give rise to semi-infinite matrices $B_{l}$, $l = 1,2,3,4$, defined by

$$
\begin{array}{l l} (B _ {1}) _ {m n} = \sqrt {m n} b _ {- m, - n}, & (B _ {2}) _ {m n} = \sqrt {m n} b _ {- m, n}, \\ (B _ {3}) _ {m n} = \sqrt {m n} b _ {m, - n}, & (B _ {4}) _ {m n} = \sqrt {m n} b _ {m n}. \end{array}
$$

From generalized Grunsky equality it immediately follows that matrices $B_{l}$ define bounded linear operators on the separable Hilbert space

$$
\ell^ {2} = \left\{x = \{x _ {n} \} _ {n = 1} ^ {\infty}: \sum_ {n = 1} ^ {\infty} | x _ {n} | ^ {2} <   \infty \right\}
$$

which we continue to denote by $B_{l}, l = 1,2,3,4$. Here a linear operator $A$ on $\ell^2$ associated with the matrix $\{a_{mn}\}_{m,n=1}^{\infty}$ is given by $y = Ax$, where $y_{m} = \sum_{n=1}^{\infty} a_{mn} x_{n}$.

<!-- page 81 of 136 -->

72

2. KÄHLER POTENTIAL AND PERIOD MAPPING

In terms of the operators $B_{l}$, generalized Grunsky equality (2.1) is equivalent to

$$
\begin{array}{l l} B _ {1} B _ {1} ^ {*} + B _ {2} B _ {2} ^ {*} = I, & \quad B _ {3} B _ {1} ^ {*} + B _ {4} B _ {2} ^ {*} = 0, \\ B _ {1} B _ {3} ^ {*} + B _ {2} B _ {4} ^ {*} = 0, & \quad B _ {3} B _ {3} ^ {*} + B _ {4} B _ {4} ^ {*} = I, \end{array}\tag{2.2}
$$

where $I$ is the identity operator on $\ell^2$ and $B_l^*$ stands for the adjoint operator to $B_l$. These identities immediately imply that $\| B_l\| \leq 1$, $l = 1, 2, 3, 4$.

REMARK 2.3. The operator $B_4$ is the Grunsky operator associated to the univalent function $g$. The classical Grunsky inequality (see e.g. [Pom92]) can be succinctly stated as $I - B_4B_4^* \geq 0$, and $I - B_4B_4^*$ is a positive-definite operator if and only if the complement of $g(\mathbb{D}^*)$ has positive Lebesgue measure. Similarly, $B_1$ is the Grunsky operator associated to the univalent function $f$ and the classical Grunsky inequality is equivalent to $I - B_1B_1^* \geq 0$. For the pair $(\mathrm{f}^\mu, \mathrm{g}_\mu)$ associated to a point $[\mu] \in T(1)$, the operators $I - B_1B_1^*$ and $I - B_4B_4^*$ are positive-definite, so that $\| B_1 \|, \| B_4 \| < 1$ and $\mathrm{Ker} B_2^* = \mathrm{Ker} B_3^* = \{0\}$. Moreover, it follows from symmetry property of Grunsky coefficients that also $\mathrm{Ker} B_2 = \mathrm{Ker} B_3 = \{0\}$, so that the operators $B_2, B_3: \ell^2 \to \ell^2$ are topological isomorphisms.

The operators $B_{l}$ define a bounded linear operator $\mathbf{B}$ on the Hilbert space $\ell^2 \oplus \ell^2$ by

$$
\mathbf {B} = \left( \begin{array}{c c} B _ {1} & B _ {2} \\ B _ {3} & B _ {4} \end{array} \right).
$$

Since

$$
\mathbf {B} ^ {*} = \left( \begin{array}{c c} B _ {1} ^ {*} & B _ {3} ^ {*} \\ B _ {2} ^ {*} & B _ {4} ^ {*} \end{array} \right),
$$

the generalized Grunsky equality can be succinctly rewritten as

$$
\mathrm{BB} ^ {*} = \mathrm{I},
$$

where $\mathbf{I} = \left( \begin{array}{cc}I & 0\\ 0 & I \end{array} \right)$ is the identity operator on $\ell^2\oplus \ell^2$. Let $J$ be the complex-conjugation operator on $\ell^2$ defined by

$$
(J x) _ {n} = \bar {x} _ {n}, \quad x = \{x _ {n} \} _ {n = 1} ^ {\infty} \in \ell^ {2}.\tag{2.3}
$$

Setting $\mathbf{J} = \left( \begin{array}{cc}J & 0\\ 0 & J \end{array} \right)$, we can express symmetry property of Grunsky coefficients as

$$
\mathrm{B} ^ {*} = \mathrm{JBJ}.
$$

Thus

$$
\mathrm{B} ^ {*} \mathrm{B} = \mathrm{JBJB} = \mathrm{JBB} ^ {*} \mathrm{J} = \mathrm{I},
$$

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026for download from IP 130.34.46.51.

so that $\mathbf{B}$ is a unitary operator on $\ell^2\oplus \ell^2$

The operators $B_{l}$ can be also realized as linear operators from the Hilbert spaces of antiholomorphic functions to the Hilbert spaces of holomorphic functions.

<!-- page 82 of 136 -->

2. GRUNSKY OPERATORS FOR  $T_{0}(1)$

73

Namely, the kernels

$$
K _ {1} (z, w) = \frac {1}{\pi} \left(\frac {1}{(z - w) ^ {2}} - \frac {f ^ {\prime} (z) f ^ {\prime} (w)}{(f (z) - f (w)) ^ {2}}\right) = \frac {1}{\pi} \sum_ {n, m = 1} ^ {\infty} n m b _ {- n, - m} z ^ {n - 1} w ^ {m - 1},
$$

$$
K _ {2} (z, w) = \frac {1}{\pi} \frac {f ^ {\prime} (z) g ^ {\prime} (w)}{(f (z) - g (w)) ^ {2}} = \frac {1}{\pi} \sum_ {n, m = 1} ^ {\infty} n m b _ {- n, m} z ^ {n - 1} w ^ {- m - 1},
$$

$$
K _ {3} (z, w) = \frac {1}{\pi} \frac {g ^ {\prime} (z) f ^ {\prime} (w)}{(g (z) - f (w)) ^ {2}} = \frac {1}{\pi} \sum_ {n, m = 1} ^ {\infty} n m b _ {n, - m} z ^ {- n - 1} w ^ {m - 1},
$$

$$
K _ {4} (z, w) = \frac {1}{\pi} \left(\frac {1}{(z - w) ^ {2}} - \frac {g ^ {\prime} (z) g ^ {\prime} (w)}{(g (z) - g (w)) ^ {2}}\right) = \frac {1}{\pi} \sum_ {n, m = 1} ^ {\infty} n m b _ {n, m} z ^ {- n - 1} w ^ {- m - 1},
$$

define the linear operators $K_{l}$ as follows,

$$
\left| K _ {1}: \overline {{A _ {2} ^ {1} (\mathbb {D})}} \rightarrow A _ {2} ^ {1} (\mathbb {D}), \quad (K _ {1} \psi) (z) = \iint_ {\mathbb {D}} K _ {1} (z, w) \overline {{\psi (w)}} d ^ {2} w, \right|
$$

$$
\left| K _ {2}: \overline {{A _ {2} ^ {1} (\mathbb {D} ^ {*})}} \rightarrow A _ {2} ^ {1} (\mathbb {D}), \quad (K _ {2} \psi) (z) = \iint_ {\mathbb {D} ^ {*}} K _ {2} (z, w) \overline {{\psi (w)}} d ^ {2} w, \right.
$$

$$
K _ {3}: \overline {{A _ {2} ^ {1} (\mathbb {D})}} \to A _ {2} ^ {1} (\mathbb {D} ^ {*}), \qquad (K _ {3} \psi) (z) = \iint_ {\mathbb {D}} K _ {3} (z, w) \overline {{\psi (w)}} d ^ {2} w,
$$

$$
K _ {4}: \overline {{A _ {2} ^ {1} (\mathbb {D} ^ {*})}} \to A _ {2} ^ {1} (\mathbb {D} ^ {*}), \qquad (K _ {4} \psi) (z) = \iint_ {\mathbb {D} ^ {*}} K _ {4} (z, w) \overline {{\psi (w)}} d ^ {2} w.
$$

REMARK 2.4. It is well-known that if $\phi$ is a holomorphic function on $\mathbb{D}$, then

$$
\iint_ {\mathbb {D}} \frac {\overline {{\phi (w)}}}{(z - w) ^ {2}} d ^ {2} w = 0,
$$

where the integral is understood in the principal value sense. Hence we can also represent operators $K_{1}$ and $K_{4}$ by the singular kernels

$$
- \frac {1}{\pi} \frac {f ^ {\prime} (z) f ^ {\prime} (w)}{(f (z) - f (w)) ^ {2}} \quad \text {and} \quad - \frac {1}{\pi} \frac {g ^ {\prime} (z) g ^ {\prime} (w)}{(g (z) - g (w)) ^ {2}}.
$$

The Hilbert spaces $A_2^1 (\mathbb{D})$ and $A_2^1 (\mathbb{D}^*)$ have standard orthonormal bases $\{e_n\}_{n = 1}^{\infty}$ and $\{f_n\}_{n = 1}^{\infty}$, given respectively by

$$
e _ {n} (z) = \sqrt {\frac {n}{\pi}} z ^ {n - 1} \quad \text {and} \quad f _ {n} (z) = \sqrt {\frac {n}{\pi}} z ^ {- n - 1}, \quad n \in \mathbb {N}.
$$

These bases define isomorphisms $A_2^1(\mathbb{D}) \simeq \ell^2$ and $A_2^1(\mathbb{D}^*) \simeq \ell^2$. The operators $K_l$ and their adjoints $K_l^*$ — integral operators with the kernels $K_l^*(z, w) = \overline{K_l(w, z)}$, correspond respectively to the operators $B_l$ and $B_l^*, l = 1, 2, 3, 4$. Similarly, positive self-adjoint operators $\mathsf{K}_l = K_lK_l^*$ are integral operators which correspond to the operators $B_lB_l^*$, and we denote the kernels of the operators $\mathsf{K}_l$ by $\mathsf{K}_l(z, w)$. Due to the relations (2.2),

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

$$
\mathsf {K} _ {2} = I - \mathsf {K} _ {1}, \mathsf {K} _ {3} = I - \mathsf {K} _ {4},\tag{2.4}
$$

<!-- page 83 of 136 -->

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

74

2. KÄHLER POTENTIAL AND PERIOD MAPPING

LEMMA 2.5. The kernel $K_{1}(z,w)$ of the operator $K_{1}:A_{2}^{1}(\mathbb{D})\to A_{2}^{1}(\mathbb{D})$ satisfies

$$
\left| \iint_ {\mathbb {D}} \iint_ {\mathbb {D}} | K _ {1} (z, w) | ^ {2} d ^ {2} z d ^ {2} w <   \infty \right|\tag{2.5}
$$

if and only if the operator $K_{1}$ is Hilbert-Schmidt, i.e., if and only if the operator $\mathsf{K}_1 = K_1K_1^*$ on $A_2^1(\mathbb{D})$ is of trace class. In this case,

$$
\mathrm{Tr}   \mathsf {K} _ {1} = \iint_ {\mathbb {D}} \iint_ {\mathbb {D}} | K _ {1} (z, w) | ^ {2} d ^ {2} z d ^ {2} w = \iint_ {\mathbb {D}} \mathsf {K} _ {1} (z, z) d ^ {2} z,
$$

and $S(f) \in A_2(\mathbb{D})$, where $f$ is the univalent function associated with the kernel $K_1(z, w)$. Similar statements hold for the operators $K_4$ and $K_4$.

PROOF. It is sufficient to prove the lemma for the operator $K_{1}$. For the basis $\{e_n\}_{n\in \mathbb{N}}$ of the Hilbert space $A_2^1 (\mathbb{D})$ we have

$$
\begin{array}{c} \hline \mathrm{Tr}   \mathsf {K} _ {1} = \sum_ {n = 1} ^ {\infty} \langle \mathsf {K} _ {1} e _ {n}, e _ {n} \rangle = \sum_ {n = 1} ^ {\infty} \| K _ {1} ^ {*} e _ {n} \| ^ {2} = \sum_ {n, m = 1} ^ {\infty} n m | b _ {- n, - m} | ^ {2} \\ = \iint_ {\mathbb {D}} \iint_ {\mathbb {D}} | K _ {1} (z, w) | ^ {2}   d ^ {2} z d ^ {2} w = \iint_ {\mathbb {D}} \mathsf {K} _ {1} (z, z) d ^ {2} z. \end{array}
$$

Since the operator $\mathsf{K}_1$ is positive, it is of trace class if and only if the inequality (2.5) holds. On the other hand, we have

$$
\mathcal {S} (f) (z) = - 6 \pi \lim _ {w \to z} K _ {1} (z, w) = - 6 \sum_ {n = 2} ^ {\infty} \left(\sum_ {k + l = n} k l b _ {- k, - l}\right) z ^ {n - 2}.
$$

Hence if the inequality (2.5) holds,

$$
\begin{array}{r l} \| \mathcal {S} (f) \| _ {2} ^ {2} = & 1 8 \pi \sum_ {n = 2} ^ {\infty} \frac {1}{n ^ {3} - n} \left| \sum_ {k = 1} ^ {n - 1} k (n - k) b _ {- k, - (n - k)} \right| ^ {2} \\ & \leq 1 8 \pi \sum_ {n = 2} ^ {\infty} \frac {1}{n ^ {3} - n} \left(\sum_ {k = 1} ^ {n - 1} k (n - k)\right) \left(\sum_ {k = 1} ^ {n - 1} k (n - k) | b _ {- k, - (n - k)} | ^ {2}\right) \\ & = 3 \pi \sum_ {n = 2} ^ {\infty} \sum_ {k = 1} ^ {n - 1} k (n - k) | b _ {- k, - (n - k)} | ^ {2} = 3 \pi \sum_ {n, m = 1} ^ {\infty} n m | b _ {- n, - m} | ^ {2} <   \infty . \end{array}
$$

THEOREM 2.6. If the pair $(\mathrm{f}^{\mu},\mathrm{g}_{\mu})$ corresponds to a point $[\mu ]\in T_0(1)$, then the operators $\mathsf{K}_1$ and $\mathsf{K}_4$ associated to $\mathrm{f}^{\mu}$ and $\mathrm{g}_{\mu}$ respectively, are of trace class.

PROOF. According to Lemma 2.5, it is sufficient to show that

$$
\iint_ {\mathbb {D}} \mathsf {K} _ {1} (z, z) d ^ {2} z <   \infty \text {and} \iint_ {\mathbb {D} ^ {*}} \mathsf {K} _ {4} (z, z) d ^ {2} z <   \infty .
$$

For $[\mu] \in T_0(1)$ choose a representative $\mu \in L^2(\mathbb{D}^*, \rho(z)d^2z) \cap \mathcal{O}(\mathbb{D}^*)_1$. It follows from Lemma 2.9 in Chapter 1 that the path $[t\mu]$ connecting 0 to $[\mu]$ in $T(1)$ lies on $T_0(1)$. Let $w_{t\mu} = \mathrm{g}_{t\mu}^{-1} \circ \mathrm{f}^{t\mu}$ be the corresponding conformal welding and denote by $(K_1)_t(z, w)$ the kernel $K_1(z, w)$ associated with the univalent function $\mathrm{f}^{t\mu}$. We have the following lemma.

<!-- page 84 of 136 -->

2. GRUNSKY OPERATORS FOR $T_0(1)$

75

LEMMA 2.7.

$$
\begin{array}{c} \left| \frac {d}{d s} \right| _ {s = 0} \left(K _ {1}\right) _ {s + t} \left(\mathrm{f} _ {t} ^ {- 1} (z), \mathrm{f} _ {t} ^ {- 1} (w)\right) \left(\mathrm{f} _ {t} ^ {- 1}\right) ^ {\prime} (z) \left(\mathrm{f} _ {t} ^ {- 1}\right) ^ {\prime} (w) \\ = \frac {1}{\pi^ {2}} \iint_ {\Omega_ {t} ^ {*}} \frac {\mu_ {t} (u)}{(u - z) ^ {2} (u - w) ^ {2}} d ^ {2} u, \end{array}\tag{2.6}
$$

where $\Omega_t^* = \mathrm{f}^{t\mu}(\mathbb{D}^*) = \mathrm{g}_{t\mu}(\mathbb{D}^*)$,

$$
(\mu_ {t} \circ \mathrm{g} _ {t \mu}) \frac {\overline {{\mathrm{g} _ {t \mu} ^ {\prime}}}}{\mathrm{g} _ {t \mu} ^ {\prime}} = D _ {t \mu} R _ {(t \mu) ^ {- 1}} (\mu),
$$

and the integral (2.6) is understood in the principal value sense.

PROOF. Set $w_{t} = w_{t\mu}, \mathrm{f}_{t} = \mathrm{f}^{t\mu}, \mathrm{g}_{t} = \mathrm{g}_{t\mu}$ and $v_{s} = \mathrm{f}_{s + t} \circ \mathrm{f}_{t}^{-1}$. We have

$$
v _ {s} \circ \mathrm{g} _ {t} = \mathrm{g} _ {s + t} \circ w _ {s + t} \circ w _ {t} ^ {- 1},
$$

so that $v_{s}$ is a q.c. mapping which is holomorphic on $\Omega_t = \mathrm{f}_t(\mathbb{D})$ and has Beltrami differential $\mu_{s,t}$ on $\Omega_t^*$ with

$$
(\mu_ {s, t} \circ \mathrm{g} _ {t}) \frac {\overline {{\mathrm{g} _ {t} ^ {\prime}}}}{\overline {{\mathrm{g} _ {t} ^ {\prime}}}} = \frac {(w _ {s + t} \circ w _ {t} ^ {- 1}) _ {\bar {z}}}{(w _ {s + t} \circ w _ {t} ^ {- 1}) _ {z}}.
$$

It follows from the standard variational formula for q.c. mappings that

$$
\left. \frac {d}{d s} \right| _ {s = 0} v _ {s} (z) = - \frac {1}{\pi} \iint_ {\Omega_ {*} ^ {*}} \frac {\mu_ {t} (u) z (z - 1)}{(u - z) u (u - 1)} d ^ {2} u + p (z),\tag{2.7}
$$

where $p(z)$ is a degree two polynomial. We have

$$
\begin{array}{c} (K _ {1}) _ {s + t} \left(\mathrm{f} _ {t} ^ {- 1} (z), \mathrm{f} _ {t} ^ {- 1} (w)\right) \left(\mathrm{f} _ {t} ^ {- 1}\right) ^ {\prime} (z) \left(\mathrm{f} _ {t} ^ {- 1}\right) ^ {\prime} (w) \\ = \frac {1}{\pi} \frac {\left(\mathrm{f} _ {t} ^ {- 1}\right) ^ {\prime} (z) \left(\mathrm{f} _ {t} ^ {- 1}\right) ^ {\prime} (w)}{\left(\mathrm{f} _ {t} ^ {- 1} (z) - \mathrm{f} _ {t} ^ {- 1} (w)\right) ^ {2}} - \frac {1}{\pi} \frac {v _ {s} ^ {\prime} (z) v _ {s} ^ {\prime} (w)}{(v _ {s} (z) - v _ {s} (w)) ^ {2}}, \end{array}
$$

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

and

$$
\left. \frac {d}{d s} \right| _ {s = 0} \frac {v _ {s} ^ {\prime} (z) v _ {s} ^ {\prime} (w)}{(v _ {s} (z) - v _ {s} (w)) ^ {2}} = - \frac {1}{\pi} \iint_ {\Omega^ {*}} \frac {\mu_ {t} (u)}{(u - z) ^ {2} (u - w) ^ {2}} d ^ {2} u,
$$

so that the result follows.

<!-- page 85 of 136 -->

76

2. KÄHLER POTENTIAL AND PERIOD MAPPING

Now we use the fundamental theorem of calculus to estimate

$$
\begin{array}{l} \iint_ {\mathbb {D}} \mathsf {K} _ {1} (z, z) d ^ {2} z = \iint_ {\mathbb {D}} \iint_ {\mathbb {D}} \big | (K _ {1}) _ {1} (z, w) \big | ^ {2} d ^ {2} z d ^ {2} w \\ \qquad \qquad = \iint_ {\mathbb {D}} \iint_ {\mathbb {D}} \left| \int_ {0} ^ {1} \frac {d}{d t} (K _ {1}) _ {t} (z, w) d t \right| ^ {2} d ^ {2} z d ^ {2} w \\ \qquad \qquad \leq \int_ {0} ^ {1} \iint_ {\mathbb {D}} \iint_ {\mathbb {D}} \left| \frac {d}{d t} (K _ {1}) _ {t} (z, w) \right| ^ {2} d ^ {2} z d ^ {2} w d t \\ \qquad \qquad = \int_ {0} ^ {1} \iint_ {\mathbb {D}} \iint_ {\mathbb {D}} \left| \frac {d}{d s} \Big | _ {s = 0} (K _ {1}) _ {t + s} (z, w) \right| ^ {2} d ^ {2} z d ^ {2} w d t \\ \qquad \qquad = \int_ {0} ^ {1} I (t) d t. \end{array}
$$

Making a change of variables $z \mapsto \mathrm{f}_t^{-1}(z), w \mapsto \mathrm{f}_t^{-1}(w)$ in the inner integral $I(t)$, we get

$$
\begin{array}{c} I (t) = \iint_ {\Omega_ {t}} \iint_ {\Omega_ {t}} \left| \frac {d}{d s} \right| _ {s = 0} (K _ {1}) _ {t + s} \left(\mathrm{f} _ {t} ^ {- 1} (z), \mathrm{f} _ {t} ^ {- 1} (w)\right) \left(\mathrm{f} _ {t} ^ {- 1}\right) ^ {\prime} (z) \left(\mathrm{f} _ {t} ^ {- 1}\right) ^ {\prime} (w) \bigg | ^ {2} d ^ {2} z d ^ {2} w \\ = \frac {1}{\pi^ {4}} \iint_ {\Omega_ {t}} \iint_ {\Omega_ {t}} \left| \iint_ {\Omega_ {t} ^ {*}} \frac {\mu_ {t} (u)}{(u - z) ^ {2} (u - w) ^ {2}} d ^ {2} u \right| ^ {2} d ^ {2} z d ^ {2} w. \end{array}
$$

Using the inequality

$$
\iint_ {\Omega_ {t}} \frac {d ^ {2} w}{| w - z | ^ {4}} \leq 4 \pi (\rho_ {2}) _ {t} (z), z \in \Omega_ {t} ^ {*},\tag{2.8}
$$

where $(\rho_2)_t(z)$ is the density of the hyperbolic metric on $\Omega_t^*$ (see the proof of Theorem 2.3 in Chapter 1), and the fact that the Hilbert transform is an isometry on $L^2 (\mathbb{C},d^2 z)$, we obtain

$$
\begin{array}{c} I (t) \leq \frac {1}{\pi^ {2}} \iint_ {\Omega_ {t}} \iint_ {\Omega_ {t} ^ {*}} \frac {| \mu_ {t} (z) | ^ {2}}{| z - w | ^ {4}} d ^ {2} z d ^ {2} w \leq \frac {4}{\pi} \iint_ {\Omega_ {t} ^ {*}} | \mu_ {t} (z) | ^ {2} (\rho_ {2}) _ {t} (z) d ^ {2} z \\ = \frac {4}{\pi} \iint_ {\mathbb {D} ^ {*}} | \tilde {\mu} _ {t} (z) | ^ {2} \rho (z) d ^ {2} z = \frac {4}{\pi} \| \tilde {\mu} _ {t} \| _ {2} ^ {2}, \end{array}
$$

where $\tilde{\mu}_t = D_{t\mu}R_{(t\mu)^{-1}}(\mu)$. Now it follows from Remark 2.8 in Chapter 1 that there exists a constant $C$ such that

$$
\| \tilde {\mu} _ {t} \| _ {2} \leq C \| \mu \| _ {2}
$$

for all $0 \leq t \leq 1$, so that

$$
\left| \iint_ {\mathbb {D}} K _ {1} (z, z) d ^ {2} z <   \infty . \right|
$$

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

<!-- page 86 of 136 -->

2. GRUNSKY OPERATORS FOR $T_0(1)$

77

The corresponding estimate for the kernel $K_{4}(z,w)$ is proved similarly. Alternatively, using the relation (1.3) we get

$$
\mathsf {K} _ {1} ([ \mu^ {- 1} ]) (z, w) = \mathsf {K} _ {4} ([ \mu ]) \left(\frac {1}{\bar {z}}, \frac {1}{\bar {w}}\right) \frac {1}{z ^ {2}} \frac {1}{w ^ {2}}.\tag{2.9}
$$


> **[ERRATUM 4-12]** (TT:4165; Lean: `eq_2_9`, Ch2/S2_Completed4) Wrong holomorphy. The memoir's right side is antiholomorphic in z while the left side is holomorphic. On the diagonal it is not even real, though 𝖪₁(z,z) ≥ 0. The corrected form gives \|z\|⁻⁴𝖪₄(1/z̄, 1/z̄) on the diagonal, which is what TT uses afterwards (TT:4492).

Since $T_0(1)$ is a group, the inequality for the kernel $\mathsf{K}_4$ follows from the corresponding inequality for the kernel $\mathsf{K}_1$.

REMARK 2.8. Actually using the generalized Grunsky equality one can prove an estimate sharper than (2.8). Just observe that for $z \in \Omega_t^*$

$$
\iint_ {\Omega_ {t}} \frac {d ^ {2} w}{| z - w | ^ {4}} = \pi^ {2} \mathsf {K} _ {3} (g ^ {- 1} (z), g ^ {- 1} (z)) | (g ^ {- 1}) ^ {\prime} (z) | ^ {2}
$$

and that $\frac{1}{\pi(1 - z\bar{w})^2}$ is the kernel of the identity operator on $A_2^1 (\mathbb{D}^*)$. Hence the second equation in (2.4) gives,

$$
\mathsf {K} _ {3} (z, z) = \frac {1}{\pi (1 - | z | ^ {2}) ^ {2}} - \mathsf {K} _ {4} (z, z) \leq \frac {1}{\pi (1 - | z | ^ {2}) ^ {2}},
$$

and we get

$$
\iint_ {\Omega_ {t}} \frac {d ^ {2} w}{| z - w | ^ {4}} \leq \frac {\pi}{4} (\rho_ {2}) _ {t} (z).
$$

COROLLARY 2.9. Grunsky operators $B_{1}$ and $B_{4}$ associated with the pair $(\mathrm{f}^{\mu},\mathrm{g}_{\mu})$, $[\mu ]\in T(1)$, are Hilbert-Schmidt operators on $\ell^2$ if and only if $[\mu ]\in T_0(1)$.

PROOF. Under the isomorphisms  $A_{2}^{1}(\mathbb{D}) \simeq \ell^{2}$  and  $A_{2}^{1}(\mathbb{D}^{*}) \simeq \ell^{2}$ , the operators  $K_{1}$  and  $K_{4}$  correspond to the operators  $B_{1}B_{1}^{*}$  and  $B_{4}B_{4}^{*}$  respectively. Since  $\beta(T_{0}(1)) = A_{2}(\mathbb{D}) \cap \beta(T(1))$ , the “only if” part of the statement follows from Lemma 2.5.

As an application, consider the Hilbert space $\mathcal{S}_2$ of Hilbert-Schmidt operators on $\ell^2$,

$\mathcal{S}_2 = \left\{T:\ell^2\to \ell^2$ a bounded operator $\left|\| T\| _2^2 = \mathrm{Tr}TT^{*} <   \infty \right.\right\} ,$

and define the mapping $\mathcal{P}:T_0(1)\to \mathcal{S}_2$ by

$$
\mathscr {P} ([ \mu ]) = B _ {1} (\mathrm{f} ^ {\mu}), [ \mu ] \in T _ {0} (1),
$$

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

Since Grunsky coefficients characterize univalent functions up to a post-composition with Möbius transformation, the mapping P is one to one. In fact, we have a stronger result.

THEOREM 2.10. The mapping $\mathcal{P}$ is a holomorphic inclusion of the Hilbert manifold $T_0(1)$ into the Hilbert space $\mathcal{S}_2$.

PROOF. We need to show that for every $[\nu] \in T_0(1)$ and $\mu \in H^{-1,1}(\mathbb{D}^*)$, the map $\mathbb{C} \ni t \mapsto B_1(t) = B_1(f^{\nu + t\mu})$ is holomorphic in a neighbourhood of $t = 0$ in $\mathbb{C}$. For this aim, since the mapping $[\mu] \to \mathrm{f}^\mu(z)$ is holomorphic for fixed $z \in \mathbb{D}$, for every $z, w \in \mathbb{D}$ the map

$$
t \mapsto K _ {1} ^ {\nu + t \mu} (z, w) = \frac {1}{\pi} \left(\frac {1}{(z - w) ^ {2}} - \frac {\left(\mathrm{f} ^ {\nu + t \mu}\right) ^ {\prime} (z) \left(\mathrm{f} ^ {\nu + t \mu}\right) ^ {\prime} (w)}{\left(\mathrm{f} ^ {\nu + t \mu} (z) - \mathrm{f} ^ {\nu + t \mu} (w)\right) ^ {2}}\right)
$$


> **[IMPLICIT HYPOTHESIS 4-16]** (TT:4210–4240; Lean: `thm_2_10` hypotheses, Ch2/S2_Grunsky) The proof's bound C‖ν+ζμ‖₂² needs an L² representative; TT's "ν ∈ L² ∩ L∞" is implicit in the choice of chart.
> **[ERRATUM 4-27]** (TT:4210–4240; Lean: `thm_2_10` proof (TT:4236), Ch2/S2_Grunsky (restated 2026-10-28, user-approved)) The proof of Thm 2.6 (Lemma 2.7) gives the bound only at bases in 𝒪(𝔻*)₁. At a general L² base the needed uniform HS bound requires a quasiconformal distortion lemma for harmonic L² differentials (∬\|μ∘w⁻¹\|²ρ ≤ C(K)‖μ‖₂²), which the memoir does not supply. The straight-line statement is believed true (Shen–Wei-type results) but is not proved by the memoir's argument. The chart form is the memoir's own notion of holomorphy on T₀(1) and follows from the 𝒪-base argument.

<!-- page 87 of 136 -->

78

2. KÄHLER POTENTIAL AND PERIOD MAPPING

is holomorphic in a neighbourhood of $t = 0$ in $\mathbb{C}$. We choose $\delta > 0$ so that $\| \nu + t\mu \|_{\infty} < 1$ for all $|t| < \delta$. For every $t_0$ such that $|t_0| < \delta$, let $\delta_1$ be such that $0 < \delta_1 < \delta - |t_0|$. Then for all $|t - t_0| < \delta_1$, we have by Cauchy integral formula,

$$
\begin{array}{c} \hline \left(K _ {1} ^ {\nu + t \mu} - K _ {1} ^ {\nu + t _ {0} \mu} - (t - t _ {0}) \left. \frac {d}{d t} \right| _ {t = t _ {0}} K _ {1} ^ {\nu + t \mu}\right) (z, w) \\ = \frac {(t - t _ {0}) ^ {2}}{2 \pi i} \oint_ {| \zeta - t _ {0} | = \delta_ {1}} \frac {K _ {1} ^ {\nu + \zeta \mu} (z , w)}{(\zeta - t) (\zeta - t _ {0}) ^ {2}} d \zeta . \\ \hline \end{array}
$$

Hence

(2.10)

$$
\begin{array}{c} \left\| \frac {B _ {1} (\mathrm{f} ^ {\nu + t \mu}) - B _ {1} (\mathrm{f} ^ {\nu + t _ {0} \mu})}{t - t _ {0}} - \frac {d}{d t} \Big | _ {t = t _ {0}} B _ {1} (\mathrm{f} ^ {\nu + t \mu}) \right\| _ {2} ^ {2} \\ = \iint_ {\mathbb {D}} \iint_ {\mathbb {D}} \left| \left(\frac {K _ {1} ^ {\nu + t \mu} - K _ {1} ^ {\nu + t _ {0} \mu}}{t - t _ {0}} - \frac {d}{d t} \Big | _ {t = t _ {0}} K _ {1} ^ {\nu + t \mu}\right) (z, w) \right| ^ {2} d ^ {2} z d ^ {2} w \\ \leq \frac {| t - t _ {0} | ^ {2}}{4 \pi^ {2}} \oint_ {| \zeta - t _ {0} | = \delta_ {1}} \iint_ {\mathbb {D}} \iint_ {\mathbb {D}} \left| K _ {1} ^ {\nu + \zeta \mu} (z, w) \right| ^ {2} d ^ {2} z d ^ {2} w | d \zeta | \oint_ {| \zeta - t _ {0} | = \delta_ {1}} \frac {| d \zeta |}{| \zeta - t | ^ {2} | \zeta - t _ {0} | ^ {4}}. \end{array}
$$

We have from the proof of Theorem 2.6,

$$
\iint_ {\mathbb {D}} \iint_ {\mathbb {D}} \left| K _ {1} ^ {\nu + \zeta \mu} (z, w) \right| ^ {2} d ^ {2} z d ^ {2} w \leq C \| \nu + \zeta \mu \| _ {2} ^ {2} \leq C (\| \nu \| _ {2} + \delta_ {1} \| \mu \| _ {2}) ^ {2},
$$

so that (2.10) tends to 0 as $t \to t_0$, which proves the assertion.

REMARK 2.11. Since the classical Grunsky operator $B_{1}$ is bounded, the mapping $\mathcal{P}$ extends to the whole Banach manifold $T(1)$. Let $\mathcal{B}(\ell^2)$ be the space of bounded linear operators on $\ell^2$,

$$
\left| \mathscr {B} (\ell^ {2}) = \left\{T: \ell^ {2} \to \ell^ {2} \text {a linear operator}: \| T \| = \sup _ {\| u \| = 1} \| T u \| <   \infty . \right\}, \right.
$$

and define the mapping $\hat{\mathcal{P}}:T(1)\to \mathcal{B}(\ell^2)$ by

$$
\hat {\mathcal {P}} ([ \mu ]) = B _ {1} (\mathrm{f} ^ {\mu}), \quad [ \mu ] \in T (1).
$$

Analogous to Theorem 2.10, we show in Appendix B that the mapping $\hat{\mathcal{P}}$ is a holomorphic inclusion.

2.2. Fredholm eigenvalues and Fredholm determinant. In his paper [Sch57], Schiffer has studied the eigenvalues of the classical Poincaré-Fredholm boundary value problem of potential theory on a $C^3$ curve. Here we show how Fredholm eigenvalues for a quasi-circle $\mathcal{C} = \mathrm{f}^{\mu}(S^{1}) = \mathrm{g}_{\mu}(S^{1})$, associated with $[\mu] \in T_0(1)$, are related to the eigenvalues of trace class operators $K_{1}$ and $K_{4}$.

Let $\mathfrak{h}$ be a separable Hilbert space with the inner product $\langle ,\rangle$. A conjugation operator $J$ on $\mathfrak{h}$ is an $\mathbb{R}$-linear operator satisfying $J^2 = I$ and

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026for download from IP 130.34.46.51.

$$
(J x, J y) = (\overline {{x , y}}) \quad \text {for all} \quad x, y \in \mathfrak {h}.
$$

<!-- page 88 of 136 -->

2. GRUNSKY OPERATORS FOR $T_0(1)$

79

Conjugation operator is necessarily complex anti-linear. For every bounded linear operator $T$ on $\mathfrak{h}$,

$$
\langle J T J x, y \rangle = \overline {{\langle T J x , J y \rangle}} = \overline {{\langle J x , T ^ {*} J y \rangle}} = \langle x, J T ^ {*} J y \rangle \quad \text {for all} \quad x, y \in \mathfrak {h},
$$

so that

$$
(J T J) ^ {*} = J T ^ {*} J.
$$

In particular, if $U$ is a unitary operator on $\mathfrak{h}$, then $JUJ$ is also a unitary operator. For a bounded linear operator $T$ on $\mathfrak{h}$ its transpose is defined as

$$
T ^ {t} = J T ^ {*} J.
$$

Generalizing the notion of symmetric complex-valued matrix, a bounded operator $T$ on $\mathfrak{h}$ is called symmetric with respect to the conjugation $J$, if

$$
T = T ^ {t}.
$$

The Hilbert space $\mathfrak{h} = \ell^2$ carries a standard conjugation operator $J$, defined by (2.3). The following statement is a generalization of Schur's Lemma (see, e.g., [Pom92, Sect. 3.6]) to the case of compact operators on $\ell^2$.

LEMMA 2.12. Let $T$ be a compact operator on $\ell^2$, symmetric with respect to the standard conjugation operator $J$. Then there exist a unitary operator $U$ on $\ell^2$ and an operator $D \geq 0$ on $\ell^2$, diagonal with respect to the standard basis for $\ell^2$, such that

$$
T = U D U ^ {t}.
$$

PROOF. As in [Pom92], consider the decomposition

$$
T = \frac {T + J T J}{2} + i \frac {T - J T J}{2 i} = A + i B,
$$

where $A$ and $B$ are self-adjoint compact operators satisfying $AJ = JA$ and $BJ = JB$. Let $\mathbf{T}$ be the self-adjoint operator on the Hilbert space $\ell^2 \oplus \ell^2$ defined by

$$
\mathbf {T} = \left( \begin{array}{c c} A & B \\ B & - A \end{array} \right).
$$

The operator $\mathbf{T}$ is compact and satisfies

$$
\mathbf {T E} = - \mathbf {E T} \quad \text {and} \quad \mathbf {T J} = \mathbf {J T},\tag{2.11}
$$

where

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

$$
\mathbf {E} = \left( \begin{array}{c c} 0 & - I \\ I & 0 \end{array} \right) \quad \text {and} \quad \mathbf {J} = \left( \begin{array}{c c} J & 0 \\ 0 & J \end{array} \right).
$$

From the first equation in (2.11) it follows that if $\mathbf{u} \in \ell^2 \oplus \ell^2$ is an eigenvector for $\mathbf{T}$ with eigenvalue $\lambda$, then $\mathbf{v} = \mathbf{E}\mathbf{u}$ is also an eigenvector for $\mathbf{T}$ with eigenvalue $-\lambda$. It follows from Hilbert-Schmidt theorem on canonical form of compact self-adjoint operator that there exist a unitary operator $\mathbf{U}$ on $\ell^2 \oplus \ell^2$ of the form

$$
\mathbf {U} = \left( \begin{array}{c c} U _ {1} & U _ {2} \\ U _ {2} & - U _ {1} \end{array} \right),
$$

and an operator $\mathbf{D}$ on $\ell^2\oplus \ell^2$ of the form

$$
\mathbf {D} = \left( \begin{array}{c c} D & 0 \\ 0 & - D \end{array} \right),
$$

<!-- page 89 of 136 -->

80

2. KÄHLER POTENTIAL AND PERIOD MAPPING

where $D$ is diagonal with non-negative entries, such that

$$
\mathbf {T} = \mathbf {U D U} ^ {*}.
$$

From the second equation in (2.11) it follows that $\mathbf{T}(\mathbf{JUJ}) = (\mathbf{JUJ})\mathbf{D}$. Since $\mathbf{JUJ}$ is also a unitary operator, we have

$$
\mathbf {T} = (\mathbf {J U J}) \mathbf {D} (\mathbf {J U J}) ^ {*}
$$

Consequently, we can choose $\mathbf{U}$ so that $\mathbf{U} = \mathbf{J}\mathbf{U}\mathbf{J}$. Now it follows from the canonical form that

$$
T = A + i B = (U _ {1} + i U _ {2}) D (U _ {1} ^ {*} + i U _ {2} ^ {*}).
$$

Let $U = U_{1} + iU_{2} : \ell^{2} \to \ell^{2}$. Since $\mathbf{U}$ is a unitary operator, $U$ is also unitary, and the property $\mathbf{U}^{*} = \mathbf{J}\mathbf{U}^{*}\mathbf{J}$ implies that

$$
J U ^ {*} J = J (U _ {1} ^ {*} - i U _ {2} ^ {*}) J = U _ {1} ^ {*} + i U _ {2} ^ {*},
$$

since $J$ is complex anti-linear.

COROLLARY 2.13. The non-zero entries of the operator $D$ are singular values of the operator $T$.

PROOF. Since the operator $U^t$ is unitary,

$$
T T ^ {*} = U D ^ {2} U ^ {*} = U D ^ {2} U ^ {- 1},
$$

so that the entries of $D^2$ are the eigenvalues of $TT^*$.

Now let $(f,g)$ be a normalized disjoint pair of univalent functions such that the corresponding set $F$ has Lebesgue measure zero and the Grunsky operator $B_{1}$ is compact. We apply Schur's Lemma to the operator $B_{1}$ on $\ell^2$. It follows from the symmetry property of Grunsky coefficients that

$$
B _ {1} ^ {*} = J B _ {1} J.
$$

Thus there exist a unitary operator $U$ on $\ell^2$ and a diagonal operator $D$ with nonnegative entries such that

$$
B _ {1} = U D U ^ {t}.
$$

From the first identity in (2.2), we obtain

$$
U ^ {- 1} B _ {2} B _ {2} ^ {*} U = I - D ^ {2},
$$

Since $\| B_1 \| < 1$, the operator $I - D^2$ is positive-definite and hence invertible, so that the operator

$$
V = B _ {2} ^ {*} U (I - D ^ {2}) ^ {- 1 / 2}
$$

is also unitary. Using the property $B_3^t = B_2$, which follows from the symmetry of Grunsky coefficients, and the third identity in (2.2), we obtain

$$
V ^ {t} B _ {4} V = - D.
$$

Collecting everything together, we get the following identities:

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026for download from IP 130.34.46.51.

$$
\left| \begin{array}{c c} B _ {1} J U J = U D, & B _ {3} J U J = J V J (I - D ^ {2}) ^ {1 / 2}, \\ B _ {2} V = U (I - D ^ {2}) ^ {1 / 2}, & B _ {4} V = - J V J D. \end{array} \right.
$$

<!-- page 90 of 136 -->

2. GRUNSKY OPERATORS FOR $T_0(1)$

81

Letting

$$
\begin{array}{c} \lambda_ {n} = (D) _ {n n}, \qquad \rho_ {n} = ((1 - D ^ {2}) ^ {1 / 2}) _ {n n} = \sqrt {1 - \lambda_ {n} ^ {2}} \\ \mathfrak {u} _ {n} (z) = \sum_ {m = 1} ^ {\infty} \sqrt {\frac {m}{\pi}} U _ {m n} z ^ {m - 1}, \quad \mathfrak {v} _ {n} (z) = \sum_ {m = 1} ^ {\infty} \sqrt {\frac {m}{\pi}} (J V J) _ {m n} z ^ {- m - 1}, \end{array}
$$

and realizing $B_{l}$'s as linear operators $K_{l}$'s, we obtain for $n \in \mathbb{N}$,

$$
\begin{array}{l l} \iint_ {\mathbb {D}} K _ {1} (z, w) \overline {{\mathfrak {u} _ {n} (w)}} d ^ {2} w = \lambda_ {n} \mathfrak {u} _ {n} (z), & \iint_ {\mathbb {D}} K _ {3} (z, w) \overline {{\mathfrak {u} _ {n} (w)}} d ^ {2} w = \rho_ {n} \mathfrak {v} _ {n} (z) \\ \iint_ {\mathbb {D} ^ {*}} K _ {2} (z, w) \overline {{\mathfrak {v} _ {n} (w)}} d ^ {2} w = \rho_ {n} \mathfrak {u} _ {n} (z), & \iint_ {\mathbb {D} ^ {*}} K _ {4} (z, w) \overline {{\mathfrak {v} _ {n} (w)}} d ^ {2} w = - \lambda_ {n} \mathfrak {v} _ {n} (z). \end{array}
$$

Setting

$$
u _ {n} = \mathfrak {u} _ {n} \circ f ^ {- 1} (f ^ {- 1}) ^ {\prime} \qquad \text {and} \qquad v _ {n} = \mathfrak {v} _ {n} \circ g ^ {- 1} (g ^ {- 1}) ^ {\prime},
$$

we get,

$$
\left| \frac {1}{\pi} \iint_ {\Omega} \frac {\overline {{u _ {n} (w)}}}{(z - w) ^ {2}} d ^ {2} w = - \lambda_ {n} u _ {n} (z), \quad z \in \Omega , \right.\tag{2.12}
$$

$$
\frac {1}{\pi} \iint_ {\Omega} \frac {\overline {{u _ {n} (w)}}}{(z - w) ^ {2}} d ^ {2} w = \rho_ {n} v _ {n} (z), \qquad z \in \Omega^ {*},
$$

$$
\frac {1}{\pi} \iint_ {\Omega^ {*}} \frac {\overline {{v _ {n} (w)}}}{(z - w) ^ {2}} d ^ {2} w = \rho_ {n} u _ {n} (z), \qquad z \in \Omega ,
$$

$$
\frac {1}{\pi} \iint_ {\Omega^ {*}} \frac {\overline {{v _ {n} (w)}}}{(z - w) ^ {2}} d ^ {2} w = \lambda_ {n} v _ {n} (z), \qquad z \in \Omega^ {*}.
$$

Comparing equations (2.12) with corresponding formulas in [Sch57], we find that $\{\pm \lambda_n^{-1}\}_{n = 1}^{\infty}$ are Fredholm eigenvalues associated to the quasi-circle $\mathcal{C} = f(S^1) = g(S^1)$.

REMARK 2.14. The relation between the Fredholm eigenvalues and the eigenvalues of the Grunsky operator for a $C^3$ curve was first obtained by Schiffer in [Sch81]. Specifically, in [Sch81] Schiffer has shown that Fredholm eigenvalues, defined as the eigenvalues of classical Poincaré-Fredholm integral operator on $C^3$ curve, satisfy (2.12). Furthermore, using completeness of the bases $\{u_n\}$, $\{v_n\}$ in corresponding Hilbert spaces, he proved the relation (2.2), which is equivalent to the generalized Grunsky equality with $\lambda_0 = 0$. Here we use the opposite approach. We start from the generalized Grunsky equality for the pair $(\mathrm{f}^{\mu}, \mathrm{g}_{\mu})$ for $[\mu] \in T_0(1)$ and use it for deriving all necessary properties of the Grunsky operators. In particular, we prove that the Grunsky operators $B_1$ and $B_4$ associated with $[\mu] \in T_0(1)$ are Hilbert-Schmidt. The case we consider is more general than in [Sch81] since the set of all quasi-circles $\mathrm{f}^{\mu}(S^1)$ for $[\mu] \in T_0(1)$ contains the set of all $C^3$ curves as a proper subset. In fact, we prove in Appendix B that the Grunsky operators $B_1$ and $B_4$ associated with $[\mu] \in T(1)$ are compact if and only if $[\mu] \in S$, the subgroup of symmetric homeomorphisms of $S^1$. Our analysis of the relation between singular values of Grunsky operators and Fredholm eigenvalues still holds for this case.

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026for download from IP 130.34.46.51.

<!-- page 91 of 136 -->

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026for download from IP 130.34.46.51.

82

2. KÄHLER POTENTIAL AND PERIOD MAPPING

As in [Sch59], for a pair $(f,g)$ such that the corresponding operators $K_{1}$ and $K_{4}$ are of trace class, we define the Fredholm determinant for the corresponding quasi-circle $\mathcal{C} = f(S^1)$ by

$$
\left| \operatorname{Det} _ {F} (\mathcal {C}) = \prod_ {n = 1} ^ {\infty} \rho_ {n} ^ {2} = \det (I - \mathsf {K} _ {1}) = \det (I - \mathsf {K} _ {4}). \right.
$$

Theorem 2.6 justifies the following definition.

DEFINITION 2.15. The real-valued function $S_{2}: T_{0}(1) \to \mathbb{R}$ is defined as

$$
S _ {2} ([ \mu ]) = \log \operatorname{Det} _ {F} (f ^ {\mu} (S ^ {1})), \quad [ \mu ] \in T _ {0} (1).
$$

It follows from (2.9) that

$$
\mathsf {S} _ {2} ([ \mu ]) = \mathsf {S} _ {2} ([ \mu ] ^ {- 1}), \quad [ \mu ] \in T _ {0} (1).\tag{2.13}
$$

2.3. Period matrix of 1-forms. For a normalized disjoint pair $(f,g)$ of univalent functions we set $\Omega = f(\mathbb{D})$, $\Omega^{*} = g(\mathbb{D}^{*})$, and define the Hilbert spaces

$$
\begin{array}{c} \hline A _ {2} ^ {1} (\Omega) = \left\{\psi \text {holomorphic on} \Omega : \| \psi \| _ {2} ^ {2} = \iint_ {\Omega} | \psi (z) | ^ {2} d ^ {2} z <   \infty \right\}, \\ A _ {2} ^ {1} (\Omega^ {*}) = \left\{\psi \text {holomorphic on} \Omega^ {*}: \| \psi \| _ {2} ^ {2} = \iint_ {\Omega^ {*}} | \psi (z) | ^ {2} d ^ {2} z <   \infty \right\}. \end{array}
$$

The Hilbert spaces $A_2^1(\Omega)$ and $A_2^1(\Omega^*)$ — the Hilbert spaces of holomorphic 1-forms on corresponding domains, are, respectively, naturally isomorphic to the Hilbert spaces $A_2^1(\mathbb{D})$ and $A_2^1(\mathbb{D}^*)$.

Consider generalized Faber polynomials of $g$ and $f$ defined, respectively, by [Pom92, Teo03]

$$
\begin{array}{l} \log \frac {g (z) - w}{b z} = - \sum_ {n = 1} ^ {\infty} \frac {P _ {n} (w)}{n} z ^ {- n}, \\ \log \frac {w - f (z)}{w} = \log \frac {f (z)}{z} - \sum_ {n = 1} ^ {\infty} \frac {Q _ {n} (w)}{n} z ^ {n}. \end{array}
$$

Here $P_{n}(w)$ is a polynomial of degree $n$ in $w$ and $Q_{n}(w)$ is a polynomial of degree $n$ in $1 / w$. Specifically,

$$
P _ {n} (w) = (g ^ {- 1} (w)) _ {\geqslant 0} ^ {n},
$$

the polynomial part of the $n$-th power of the inverse function $g^{-1}$, and

$$
Q _ {n} (w) = (f ^ {- 1} (w)) _ {\leq 0} ^ {- n},
$$

the principal part of the negative $n$-th power of the inverse function $f^{-1}$. Here for $S \subset \mathbb{Z}$ and a formal power series $A(w) = \sum_{n \in \mathbb{Z}} A_n w^n$ we denote $(A(w))_S = \sum_{n \in S} A_n w^n$.

<!-- page 92 of 136 -->

3. VARIATIONS OF THE FUNCTIONS $S_{1}$ AND $S_{2}$

83

Comparing the definition of Faber polynomials with the definition of Grunsky coefficients, we obtain the following relations (see, e.g. [Pom92, Teo03])

$$
\begin{array}{l l} P _ {n} (g (z)) = z ^ {n} + n \sum_ {m = 1} ^ {\infty} b _ {n m} z ^ {- m}, & P _ {n} (f (z)) = n b _ {n, 0} + n \sum_ {m = 1} ^ {\infty} b _ {n, - m} z ^ {m}, \\ Q _ {n} (g (z)) = - n b _ {- n, 0} + n \sum_ {m = 1} ^ {\infty} b _ {m, - n} z ^ {- m}, & Q _ {n} (f (z)) = z ^ {- n} + n \sum_ {m = 1} ^ {\infty} b _ {- n, - m} z ^ {m}. \end{array}
$$

Now assume that the pair $(f,g)$ is such that the corresponding set $F = \mathbb{C} \setminus \{f(\mathbb{D}) \cup g(\mathbb{D}^*)\}$ has Lebesgue measure zero. Then it follows from the above formulas and Remark 2.3 that the Hilbert spaces $A_2^1(\Omega)$ and $A_2^1(\Omega^*)$ have natural bases $\{\alpha_n\}_{n=1}^\infty$ and $\{\beta_n\}_{n=1}^\infty$, given respectively by the polynomials

$$
\alpha_ {n} (z) = \frac {P _ {n} ^ {\prime} (z)}{\sqrt {\pi n}}, \quad n \in \mathbb {N},
$$

and by the Laurent polynomials

$$
\beta_ {n} (z) = \frac {Q _ {n} ^ {\prime} (z)}{\sqrt {\pi n}}, \quad n \in \mathbb {N}.
$$

Indeed, we have

$$
\alpha_ {n} \circ f f ^ {\prime} = \sum_ {m = 1} ^ {\infty} (B _ {3}) _ {n m} e _ {m} \quad \text {and} \quad \beta_ {n} \circ g g ^ {\prime} = \sum_ {m = 1} ^ {\infty} (B _ {2}) _ {n m} f _ {m},
$$

and the inner products are given by

$$
\begin{array}{l} \langle \alpha_ {n}, \alpha_ {m} \rangle = \iint_ {\Omega} \alpha_ {n} (z) \overline {{\alpha_ {m} (z)}} d ^ {2} z = \iint_ {\mathbb {D}} \alpha_ {n} (f (z)) f ^ {\prime} (z) \overline {{\alpha_ {m} (f (z)) f ^ {\prime} (z)}} d ^ {2} z \\ \qquad = \sum_ {k = 1} ^ {\infty} (B _ {3}) _ {n k} \overline {{(B _ {3})}} _ {m k}. \end{array}
$$

Hence the period matrix of $A_2^1(\Omega)$ with respect to the basis $\{\alpha_n\}_{n=1}^{\infty}$ of holomorphic 1-forms on $\Omega$ (the Gram matrix of the basis) is given by

$$
N _ {\Omega} = \{\langle \alpha_ {n}, \alpha_ {m} \rangle \} _ {m, n = 1} ^ {\infty} = B _ {3} B _ {3} ^ {*}.
$$

Similarly, the period matrix of the basis $\{\beta_n\}_{n=1}^{\infty}$ of holomorphic 1-forms on $\Omega^{*}$ is given by

$$
N _ {\Omega^ {*}} = \{\langle \beta_ {n}, \beta_ {m} \rangle \} _ {m, n = 1} ^ {\infty} = B _ {2} B _ {2} ^ {*}.
$$

We just proved the following result.

COROLLARY 2.16. Let $(f,g)$ be a normalized disjoint pair of univalent functions such that the set $F = \mathbb{C} \setminus \{f(\mathbb{D}) \cup g(\mathbb{D}^*)\}$ has Lebesgue measure zero and the corresponding Grunsky operators $B_1$ and $B_4$ are Hilbert-Schmidt. Then for $\mathcal{C} = f(S^1)$,

$$
\mathrm{Det} _ {F} (\mathcal {C}) = \det N _ {\Omega} = \det N _ {\Omega^ {*}}
$$

## 3. Variations of the functions $S_{1}$ and $S_{2}$

Let $\partial$ and $\bar{\partial}$ be $(1,0)$ and $(0,1)$ components of de Rham differential $d$ on the complex manifold $T_0(1)$. Here we compute the "first variations" of the functions $\mathsf{S}_1$ and $\mathsf{S}_2$ — the $(1,0)$-forms $\partial\mathsf{S}_1$ and $\partial\mathsf{S}_2$ on $T_0(1)$.

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026for download from IP 130.34.46.51.

<!-- page 93 of 136 -->

84

2. KÄHLER POTENTIAL AND PERIOD MAPPING

## 3.1. The first variation of $S_{2}$.

THEOREM 3.1. The real-valued function $S_2 : T_0(1) \to \mathbb{R}$ is differentiable at every point $[\nu] \in T_0(1)$. In terms of the Bers coordinates $\varepsilon_\mu$ on the chart $V_\nu$,

$$
\left| \frac {\partial \mathsf {S} _ {2}}{\partial \varepsilon_ {\mu}} ([ \nu ]) = - \frac {1}{6 \pi} \iint_ {\mathbb {D} ^ {*}} \mathcal {S} (\mathrm{g} _ {\nu}) (z) \mu (z) d ^ {2} z. \right|
$$

Here $w_{\nu} = \mathrm{g}_{\nu}^{-1}\circ \mathrm{f}^{\nu}$ is the conformal welding corresponding to $[\nu ]\in T_0(1)$.

PROOF. By definition of the Bers coordinates (see Section 2.3. in Chapter 1), for $\mu \in H^{-1,1}(\mathbb{D}^*)$

$$
\frac {\partial \mathsf {S} _ {2}}{\partial \varepsilon_ {\mu}} ([ \nu ]) = \left. \frac {d}{d \varepsilon} \right| _ {\varepsilon = 0} \mathsf {S} _ {2} ([ \varepsilon \mu * \nu ]).
$$

Set $w_{\varepsilon \mu} \circ w_{\nu} = \mathrm{g}_{\varepsilon}^{-1} \circ \mathrm{f}^{\varepsilon}$, $\mathrm{f} = \mathrm{f}^{0} = \mathrm{f}^{\nu}$, $\mathrm{g} = \mathrm{g}_{0} = \mathrm{g}_{\nu}$ and $K_{1}(\varepsilon) = K_{1}(\mathrm{f}^{\varepsilon})$. Since $K_{1}(\varepsilon)$ is a holomorphic family, we have

$$
\frac {\partial S _ {2}}{\partial \varepsilon_ {\mu}} ([ \nu ]) = \left. \frac {\partial}{\partial \varepsilon} \right| _ {\varepsilon = 0} \log \det (I - \mathsf {K} _ {1} (\varepsilon)) = - \operatorname{Tr} \left((I - \mathsf {K} _ {1}) ^ {- 1} \frac {\partial \mathsf {K} _ {1}}{\partial \varepsilon} (0)\right)\tag{3.1}
$$

(see, e.g., [GK69, Ch. IV.1, Property 9]). Now using Lemma 2.7, we have

$$
\begin{array}{l} \frac {\partial K _ {1}}{\partial \varepsilon_ {\mu}} ([ \nu ]) (z, w) = \frac {1}{\pi^ {2}} \iint_ {\mathbb {D}} \iint_ {\mathbb {D} ^ {*}} \frac {\mu (u) f ^ {\prime} (z) g ^ {\prime} (u) ^ {2} f ^ {\prime} (\zeta)}{(f (z) - g (u)) ^ {2} (g (u) - f (\zeta)) ^ {2}} K _ {1} ^ {*} (\zeta , w) d ^ {2} u d ^ {2} \zeta \\ \qquad = \iint_ {\mathbb {D}} \iint_ {\mathbb {D} ^ {*}} \mu (u) K _ {2} (z, u) K _ {3} (u, \zeta) K _ {1} ^ {*} (\zeta , w) d ^ {2} u d ^ {2} \zeta \\ \qquad = - \iint_ {\mathbb {D} ^ {*}} \iint_ {\mathbb {D} ^ {*}} \mu (u) K _ {2} (z, u) K _ {4} (u, \zeta) K _ {2} ^ {*} (\zeta , w) d ^ {2} u d ^ {2} \zeta . \end{array}
$$

Here in the last line, we have used the second relation in (2.2),

$$
K _ {3} K _ {1} ^ {*} = - K _ {4} K _ {2} ^ {*}
$$

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

Let $R_{2}(z,w)$ be the kernel of the inverse operator $K_{2}^{-1}$ — the anti-holomorphic function on $D^{*}\times D$ satisfying

$$
\begin{array}{l} \iint_ {\mathbb {D} ^ {*}} K _ {2} (z, \zeta) R _ {2} (\zeta , w) d ^ {2} \zeta = I _ {1} (z, w) = \frac {1}{\pi (1 - z \bar {w}) ^ {2}}, \\ \iint_ {\mathbb {D}} R _ {2} (z, \zeta) K _ {2} (\zeta , w) d ^ {2} \zeta = I _ {2} (z, w) = \frac {1}{\pi (1 - \bar {z} w) ^ {2}}. \end{array}
$$

Here $I_1(z, w)$ and $I_2(z, w)$ are the kernels of the identity operators on $A_2^1(\mathbb{D})$ and $\overline{A_2^1(\mathbb{D}^*)}$ respectively. Similarly, let $R_2^*(z, w)$ be the kernel of the inverse operator $(K_2^*)^{-1}$. We have

$$
(I - \mathsf {K} _ {1}) ^ {- 1} = \mathsf {K} _ {2} ^ {- 1} = (K _ {2} ^ {*}) ^ {- 1} K _ {2} ^ {- 1},
$$

<!-- page 94 of 136 -->

3. VARIATIONS OF THE FUNCTIONS $S_{1}$ AND $S_{2}$

85

so that

$$
\begin{array}{l} \frac {\partial S _ {2}}{\partial \varepsilon_ {\mu}} ([ \nu ]) = \iint_ {\mathbb {D}} \iint_ {\mathbb {D} ^ {*}} \iint_ {\mathbb {D}} \iint_ {\mathbb {D} ^ {*}} \iint_ {\mathbb {D} ^ {*}} \iint_ {\mathbb {D} ^ {*}} \mu (u) R _ {2} ^ {*} (w, \eta) R _ {2} (\eta , z) \\ \qquad \qquad \qquad K _ {2} (z, u) K _ {4} (u, \zeta) K _ {2} ^ {*} (\zeta , w) d ^ {2} u d ^ {2} \zeta d ^ {2} z d ^ {2} \eta d ^ {2} w \\ = \iint_ {\mathbb {D} ^ {*}} \iint_ {\mathbb {D} ^ {*}} \iint_ {\mathbb {D} ^ {*}} \mu (u) K _ {4} (u, \zeta) I _ {2} (\eta , u) I _ {2} (\zeta , \eta) d ^ {2} u d ^ {2} \eta d ^ {2} \zeta \\ = \iint_ {\mathbb {D} ^ {*}} \iint_ {\mathbb {D} ^ {*}} \mu (u) K _ {4} (u, \zeta) I _ {2} (\zeta , u) d ^ {2} u d ^ {2} \zeta \\ = \iint_ {\mathbb {D} ^ {*}} \mu (u) K _ {4} (u, u) d ^ {2} u = - \frac {1}{6 \pi} \iint_ {\mathbb {D} ^ {*}} \mathcal {S} (\mathrm{g} _ {\nu}) (u) \mu (u) d ^ {2} u. \end{array}
$$

Here in the last line we have used

$$
K _ {4} (u, u) = - \frac {1}{\pi} \lim _ {\zeta \to u} \left(\frac {\mathrm{g} ^ {\prime} (u) \mathrm{g} ^ {\prime} (\zeta)}{(\mathrm{g} (\zeta) - \mathrm{g} (u)) ^ {2}} - \frac {1}{(\zeta - u) ^ {2}}\right) = - \frac {1}{6 \pi} \mathcal {S} (\mathrm{g}) (u).
$$

Denote by $T_{[\mu]}^{*}T_{0}(1)$ the holomorphic cotangent space to $T_{0}(1)$ at a point $[\mu] \in T_{0}(1)$. The natural isomorphism $T_{[\mu]}T_{0}(1) \simeq H^{-1,1}(\mathbb{D}^{*})$ induces the isomorphism $T_{[\mu]}^{*}T_{0}(1) \simeq A_{2}(\mathbb{D}^{*})$. Define a holomorphic 1-form $\vartheta$ on $T_{0}(1)$ by

$$
\boldsymbol {\vartheta} _ {[ \mu ]} = \mathcal {S} (\mathrm{g} _ {\mu}) \in A _ {2} (\mathbb {D} ^ {*}),
$$

where $w_{\mu} = g_{\mu}^{-1}\circ \mathrm{f}^{\mu}\in T_0(1)$

COROLLARY 3.2. On $T_0(1)$,

$$
\partial \mathsf {S} _ {2} = - \frac {1}{6 \pi} \vartheta .
$$

REMARK 3.3. For $C^3$ curves the statement of Theorem 3.1 was obtained by Schiffer in [Sch59]. The derivation in [Sch59] uses the variational theory of Fredholm eigenvalues and the exterior variation of the domain. Our proof is different from Schiffer's: we use general formula (3.1) and the quasi-conformal variation.

3.2. The first variation of $S_1$. In addition to $S_1$, we introduce another function $\tilde{S}_1 : T_0(1) \to \mathbb{R}$ defined by

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

$$
\tilde {\mathsf {S}} _ {1} ([ \mu ]) = \mathsf {S} _ {1} ([ \mu^ {- 1} ]).
$$

Using (1.3), we get

$$
\begin{array}{r l} & {\tilde {S} _ {1} ([ \mu ]) = \iint_ {\mathbb {D}} \left| \mathcal {A} (\mathrm{f} ^ {\mu}) - 2 \frac {(\mathrm{f} ^ {\mu}) ^ {\prime}}{\mathrm{f} ^ {\mu}} + \frac {2}{z} \right| ^ {2} d ^ {2} z + \iint_ {\mathbb {D} ^ {*}} \left| \mathcal {A} (\mathrm{g} _ {\mu}) - 2 \frac {\mathrm{g} _ {\mu} ^ {\prime}}{\mathrm{g} _ {\mu}} + \frac {2}{z} \right| ^ {2} d ^ {2} z} \\ & {- 4 \pi \log | (\mathrm{g} _ {\mu}) ^ {\prime} (\infty) |} \\ & {= \iint_ {\mathbb {D}} | \mathcal {A} (\tilde {\mathrm{g}} _ {\mu}) | ^ {2} d ^ {2} z + \iint_ {\mathbb {D} ^ {*}} \left| \mathcal {A} (\tilde {\mathrm{f}} ^ {\mu}) \right| ^ {2} d ^ {2} z + 4 \pi \log | \tilde {\mathrm{g}} _ {\mu} ^ {\prime} (0) |,} \end{array}
$$

<!-- page 95 of 136 -->

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026for download from IP 130.34.46.51.

86

2. KÄHLER POTENTIAL AND PERIOD MAPPING

where $\tilde{\mathrm{f}}^{\mu} = \imath \circ \mathrm{f}^{\mu} \circ \imath$, $\tilde{\mathrm{g}}_{\mu} = \imath \circ \mathrm{g}_{\mu} \circ \imath$ and $\imath(z) = \frac{1}{z}$. The functions $\tilde{\mathrm{f}}^{\mu}$ and $\tilde{\mathrm{g}}_{\mu}$ are univalent, respectively, on the domains $\mathbb{D}^{*}$ and $\mathbb{D}$ and are normalized as $\tilde{\mathrm{f}}^{\mu}(\infty) = \infty$, $(\tilde{\mathrm{f}}^{\mu})'(\infty) = 1$ and $\tilde{\mathrm{g}}_{\mu}(0) = 0$. They satisfy the factorization

$$
\tilde {w} _ {\mu} = \tilde {\mathrm{g}} _ {\mu} ^ {- 1} \circ \tilde {\mathrm{f}} ^ {\mu},\tag{3.2}
$$

where $\tilde{w}_{\mu} = \imath \circ w_{\mu} \circ \imath$.

This description corresponds to the realization of $T(1)$ associated with the model $\mathbb{H}^2 \simeq \mathbb{D}$. Namely, due to the canonical isomorphism

$$
\mu \in L ^ {\infty} (\mathbb {D} ^ {*}) \mapsto \tilde {\mu} = \imath^ {*} \mu = \mu \left(\frac {1}{z}\right) \frac {z ^ {2}}{\bar {z} ^ {2}} \in L ^ {\infty} (\mathbb {D}),
$$

we have $T(1) \simeq L^{\infty}(\mathbb{D})_{1} / \sim$. If $w_{\mu}$ is a q.c. mapping associated with $\mu \in L^{\infty}(\mathbb{D}^{*})_{1}$, then $\tilde{w}_{\mu}$ is the q.c. mapping associated with $\tilde{\mu} \in L^{\infty}(\mathbb{D})_{1}$, and corresponding conformal wielding is given by (3.2).

In this section, we will also use the model $T(1) \simeq L^{\infty}(\mathbb{D})_1$. To simplify the notations, for $\mu \in L^{\infty}(\mathbb{D})_1$ we will denote corresponding q.c. mapping by $w_{\mu} = \mathrm{g}_{\mu}^{-1} \circ \mathrm{f}^{\mu}$, where $\mathrm{f}^{\mu}$ and $\mathrm{g}_{\mu}$ are univalent on the domains $\mathbb{D}^*$ and $\mathbb{D}$ and are normalized as $\mathrm{f}^{\mu}(\infty) = \infty$, $(\mathrm{f}^{\mu})'(\infty) = 1$ and $\mathrm{g}_{\mu}(0) = 0$. Correspondingly, for $\gamma = g^{-1} \circ f \in \mathcal{T}(1)$ we would have the normalization $f(\infty) = \infty$, $f'(\infty) = 1$ and $g(0) = 0$. To avoid confusion with the notations for our primary model $T(1) = L^{\infty}(\mathbb{D}^{*})_{1} / \sim$, we will always specify explicitly in the main text when we are using the model $T(1) \simeq L^{\infty}(\mathbb{D})_{1} / \sim$.

The function $S_{1}$ on $T_0(1)$ naturally extends to a function $\hat{S}$ on $\mathcal{T}_0(1)$, defined by

$$
\left| \hat {\mathsf {S}} (\gamma) = \iint_ {\mathbb {D}} | \mathcal {A} (f) | ^ {2} d ^ {2} z + \iint_ {\mathbb {D} ^ {*}} | \mathcal {A} (g) | ^ {2} d ^ {2} z - 4 \pi \log | g ^ {\prime} (\infty) |, \right.
$$

where $\gamma = g^{-1} \circ f \in \mathcal{T}_0(1)$. For $\tilde{\mathsf{S}}(\gamma) = \hat{\mathsf{S}}(\gamma^{-1})$ we have

$$
\tilde {S} (\gamma) = \iint_ {\mathbb {D}} | \mathcal {A} (\tilde {g}) | ^ {2} d ^ {2} z + \iint_ {\mathbb {D} ^ {*}} \left| \mathcal {A} (\tilde {f}) \right| ^ {2} d ^ {2} z + 4 \pi \log | \tilde {g} ^ {\prime} (0) |,
$$

where $\tilde{f} = \imath \circ f\circ \imath$ and $\tilde{g} = \imath \circ g\circ \imath$.

LEMMA 3.4. The function $\tilde{\mathsf{S}}$ is constant along the fibers of the canonical projection $\pi : \mathcal{T}_0(1) \to T_0(1)$, $\tilde{\mathsf{S}} = \tilde{\mathsf{S}}_1 \circ \pi$.

PROOF. We are using the model $T(1) \simeq L^{\infty}(\mathbb{D})_1 / \sim$. For $\mu \in L^{\infty}(\mathbb{D})_1$ let $\gamma = g^{-1} \circ f$, $\gamma_{\mu} = g_{\mu}^{-1} \circ f^{\mu} \in \mathcal{T}_0(1)$ be such that $\pi(\gamma) = \pi(\gamma_{\mu}) = [\mu]$. Comparing the normalization for $f$ and $f^{\mu}$ at $\infty$, we get

$$
f = \sigma \circ f ^ {\mu} \quad \text {and} \quad g = \sigma \circ g _ {\mu} \circ \alpha^ {- 1},
$$

for some $\alpha \in \mathrm{PSU}(1,1)$ and $\sigma(z) = z + b_0$. Since $f \mapsto \mathcal{A}(f)$ is invariant if $f$ is post-composed with a translation$^1$, to prove that $\tilde{\mathrm{S}}(\gamma) = \tilde{\mathrm{S}}(\gamma_\mu)$ we need only to check that for $\alpha \in \mathrm{PSU}(1,1)$,

$$
\iint_ {\mathbb {D}} | \mathcal {A} (g \circ \alpha^ {- 1}) | ^ {2} d ^ {2} z + 4 \pi \log | (g \circ \alpha^ {- 1}) ^ {\prime} (0) | = \iint_ {\mathbb {D}} | \mathcal {A} (g) | ^ {2} d ^ {2} z + 4 \pi \log | g ^ {\prime} (0) |.
$$

<small><span class="docvortex-page-footnote" data-block-type="page_footnote" style="color:#6b7280">$T(1)\simeq L^{\infty}(\mathbb{D})_{1} / \sim$</span></small>

<small><span class="docvortex-page-footnote" data-block-type="page_footnote" style="color:#6b7280">$^{1}$ This is why it is more convenient to use the model  $T(1) \simeq L^{\infty}(\mathbb{D})_{1}/\sim$ .</span></small>

<!-- page 96 of 136 -->

3. VARIATIONS OF THE FUNCTIONS $S_{1}$ AND $S_{2}$

87

Let

$$
\left| \alpha (z) = e ^ {i \theta} \frac {z - w}{1 - z \bar {w}} \right|
$$

and set $\log g'(z) = \sum_{n=0}^{\infty} a_n z^n$. Then $\mathcal{A}(g) = \sum_{n=1}^{\infty} na_n z^{n-1}$ and

$$
\begin{array}{l} \iint_ {\mathbb {D}} | \mathcal {A} (g \circ \alpha^ {- 1}) | ^ {2} d ^ {2} z = \iint_ {\mathbb {D}} | \mathcal {A} (g) \circ \alpha^ {- 1} (\alpha^ {- 1}) ^ {\prime} + \mathcal {A} (\alpha^ {- 1}) | ^ {2} d ^ {2} z \\ \qquad = \iint_ {\mathbb {D}} | \mathcal {A} (g) - \mathcal {A} (\alpha) | ^ {2} d ^ {2} z = \iint_ {\mathbb {D}} \left| \mathcal {A} (g) - \frac {2 \bar {w}}{1 - z \bar {w}} \right| ^ {2} d ^ {2} z \\ \qquad = \iint_ {\mathbb {D}} | \mathcal {A} (g) | ^ {2} d ^ {2} z - 4 \operatorname{Re} \left(w \iint_ {\mathbb {D}} \mathcal {A} (g) (z) \sum_ {n = 1} ^ {\infty} (w \bar {z}) ^ {n - 1} d ^ {2} z\right) \\ \qquad \qquad + 4 | w | ^ {2} \iint_ {\mathbb {D}} \left| \sum_ {n = 1} ^ {\infty} (w \bar {z}) ^ {n - 1} \right| ^ {2} d ^ {2} z. \end{array}
$$

The last two terms give

$$
\begin{array}{c} - 4 \pi \operatorname{Re} \left(\sum_ {n = 1} ^ {\infty} a _ {n} w ^ {n}\right) + 4 \pi \sum_ {n = 1} ^ {\infty} \frac {| w | ^ {2 n}}{n} \\ = - 4 \pi \log | g ^ {\prime} (w) | + 4 \pi \log | g ^ {\prime} (0) | - 4 \pi \log (1 - | w | ^ {2}). \end{array}
$$

On the other hand, we have

$$
(g \circ \alpha^ {- 1}) ^ {\prime} (0) = g ^ {\prime} (\alpha^ {- 1} (0)) (\alpha^ {- 1}) ^ {\prime} (0) = (1 - | w | ^ {2}) g ^ {\prime} (w).
$$

This concludes the proof.

THEOREM 3.5. The real-valued function $\tilde{\mathbb{S}}_1: T_0(1) \to \mathbb{R}$ is differentiable at every point $[\nu] \in T_0(1)$. In terms of the Bers coordinates $\varepsilon_\mu$ on the chart $V_\nu$,

$$
\frac {\partial \tilde {S} _ {1}}{\partial \varepsilon_ {\mu}} ([ \nu ]) = 2 \iint_ {\mathbb {D} ^ {*}} \mathcal {S} (\mathrm{g} _ {\nu}) (z) \mu (z) d ^ {2} z.
$$

PROOF. We are using the model $T(1) \simeq L^{\infty}(\mathbb{D})_1$. For $[\nu] \in T_0(1)$ choose a representative $\nu \in L^{\infty}(\mathbb{D})_1$ which is a product of elements in $H^{-1,1}(\mathbb{D})_1$, and let $w_{\varepsilon} = w_{\varepsilon \mu} \circ w_{\nu} = \mathrm{g}_{\varepsilon}^{-1} \circ \mathrm{f}^{\varepsilon}$. It follows from Lemma 1.5 in Chapter 1 that corresponding $\gamma_{\varepsilon} = g_{\varepsilon}^{-1} \circ f^{\varepsilon}$ fixes $0, 1, \infty$. By the above lemma,

$$
\tilde {S} _ {1} ([ \varepsilon \mu * \nu ]) = \tilde {S} (\gamma_ {\varepsilon}).
$$

We have $\gamma_{\varepsilon} \circ \gamma_{\nu}^{-1} = \gamma_{\varepsilon \kappa}$, where $\kappa = (\alpha^{-1})^{*}(\mu)$ and $\alpha = \gamma_{\nu} \circ w_{\nu}^{-1} \in \mathrm{PSU}(1,1)$. Set $f = f^0$, $g = g^0$, so that $g = \sigma \circ g_{\nu} \circ \alpha^{-1}$ for some $\sigma \in \mathrm{PSL}(2,\mathbb{C})$, and define $v_{\varepsilon} = f^{\varepsilon} \circ f^{-1}$. Since $f^{\varepsilon}$ is normalized, it's Laurent expansion at $\infty$ has the form

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

$$
f ^ {\varepsilon} (z) = z + \frac {b _ {1}}{z} + \frac {b _ {2}}{z ^ {2}} + \dots .
$$

Hence

$$
\left. \frac {\partial}{\partial \varepsilon} \right| _ {\varepsilon = 0} v _ {\varepsilon} (z) = O (z ^ {- 1}) \quad \text {as} \quad z \to \infty ,
$$

<!-- page 97 of 136 -->

88

2. KÄHLER POTENTIAL AND PERIOD MAPPING

and the first variations of $v_{\varepsilon}$ have the form

$$
\left. \frac {\partial}{\partial \varepsilon} \right| _ {\varepsilon = 0} v _ {\varepsilon} (z) = - \frac {1}{\pi} \iint_ {\Omega} \frac {((g ^ {- 1}) ^ {*} \kappa) (w)}{w - z} d ^ {2} w, \quad \left. \frac {\partial}{\partial \bar {\varepsilon}} \right| _ {\varepsilon = 0} v _ {\varepsilon} (z) = 0,
$$

where $\Omega = g(\mathbb{D})$. Since $\gamma_{\varepsilon \kappa}$ fixes $0,1,\infty$, we also have

$$
\left. \frac {\partial}{\partial \varepsilon} \right| _ {\varepsilon = 0} \gamma_ {\varepsilon \kappa} (z) = - \frac {1}{\pi} \iint_ {\mathbb {D}} \frac {z (z - 1) \kappa (w)}{(w - z) w (w - 1)} d ^ {2} w,
$$

$$
\left| \frac {\partial}{\partial \bar {\varepsilon}} \right| _ {\varepsilon = 0} \gamma_ {\varepsilon \kappa} (z) = - \frac {1}{\pi} \iint_ {\mathbb {D}} \frac {z (z - 1) \overline {{\kappa (w)}}}{(1 - \bar {w} z) \bar {w} (1 - \bar {w})} d ^ {2} w.
$$

Using $f^{\varepsilon} = v_{\varepsilon}\circ f$ , we obtain

$$
\mathcal {A} (f ^ {\varepsilon}) = \mathcal {A} (v _ {\varepsilon}) \circ f f ^ {\prime} + \mathcal {A} (f).
$$

Applying the variational formulas for $v_{\varepsilon}$, we have

$$
\left| \frac {\partial}{\partial \varepsilon} \right| _ {\varepsilon = 0} \mathcal {A} (v _ {\varepsilon}) (z) = \left. \frac {\partial^ {2}}{\partial z ^ {2}} \frac {\partial}{\partial \varepsilon} \right| _ {\varepsilon = 0} v _ {\varepsilon} (z) = - \frac {2}{\pi} \iint_ {\Omega} \frac {((g ^ {- 1}) ^ {*} \kappa) (w)}{(w - z) ^ {3}} d ^ {2} w,
$$

and hence

$$
\left. \frac {\partial}{\partial \varepsilon} \right| _ {\varepsilon = 0} \iint_ {\mathbb {D} ^ {*}} | \mathcal {A} (f ^ {\varepsilon}) | ^ {2} d ^ {2} z = - \frac {2}{\pi} \iint_ {\mathbb {D} ^ {*}} \iint_ {\mathbb {D}} \frac {\kappa (w) g ^ {\prime} (w) ^ {2} f ^ {\prime} (z)}{(g (w) - f (z)) ^ {3}} \overline {{\mathcal {A} (f) (z)}} d ^ {2} w d ^ {2} z = I _ {1}.
$$

Similarly, using

$$
g _ {\varepsilon} \circ \gamma_ {\varepsilon \kappa} = v _ {\varepsilon} \circ g,
$$

we have

$$
g _ {\varepsilon} ^ {\prime} \circ \gamma_ {\varepsilon \kappa} (\gamma_ {\varepsilon \kappa}) _ {z} = v _ {\varepsilon} ^ {\prime} \circ g g ^ {\prime},
$$

and

$$
\mathcal {A} (g _ {\varepsilon}) \circ \gamma_ {\varepsilon \kappa} (\gamma_ {\varepsilon \kappa}) _ {z} + \mathcal {A} (\gamma_ {\varepsilon \kappa}) = \mathcal {A} (v _ {\varepsilon}) \circ g g ^ {\prime} + \mathcal {A} (g),
$$

where

$$
\mathcal {A} (\gamma_ {\varepsilon \kappa}) = \frac {(\gamma_ {\varepsilon \kappa}) _ {z z}}{(\gamma_ {\varepsilon \kappa}) _ {z}}.
$$

Hence we have

$$
\left| \begin{array}{c} \frac {\partial}{\partial \varepsilon} \bigg | _ {\varepsilon = 0} g _ {\varepsilon} ^ {\prime} (0) = - g ^ {\prime \prime} (0) \left(\frac {\partial}{\partial \varepsilon} \bigg | _ {\varepsilon = 0} \gamma_ {\varepsilon \kappa}\right) (0) - g ^ {\prime} (0) \frac {\partial}{\partial z} \left(\frac {\partial}{\partial \varepsilon} \bigg | _ {\varepsilon = 0} \gamma_ {\varepsilon \kappa}\right) \\ + g ^ {\prime} (0) \frac {\partial}{\partial z} \left(\frac {\partial}{\partial \varepsilon} \bigg | _ {\varepsilon = 0} v _ {\varepsilon}\right) (0) \\ = \frac {g ^ {\prime} (0)}{\pi} \iint_ {\mathbb {D}} \kappa (w) \left(\frac {1}{w ^ {2}} - \frac {1}{w (w - 1)} - \frac {g ^ {\prime} (w) ^ {2}}{g (w) ^ {2}}\right) d ^ {2} w, \end{array} \right|
$$

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

(0)

<!-- page 98 of 136 -->

3. VARIATIONS OF THE FUNCTIONS $S_{1}$ AND $S_{2}$

89

and

$$
\begin{array}{c} \frac {\partial}{\partial \varepsilon} \bigg | _ {\varepsilon = 0} \overline {{g _ {\varepsilon} ^ {\prime} (0)}} = - \overline {{g ^ {\prime \prime} (0) \left(\frac {\partial}{\partial \bar {\varepsilon}} \bigg | _ {\varepsilon = 0} \gamma_ {\varepsilon \kappa}\right) (0)}} - \overline {{g ^ {\prime} (0) \frac {\partial}{\partial z} \left(\frac {\partial}{\partial \bar {\varepsilon}} \bigg | _ {\varepsilon = 0} \gamma_ {\varepsilon \kappa}\right) (0)}} \\ = \frac {\overline {{g ^ {\prime} (0)}}}{\pi} \iint_ {\mathbb {D}} \frac {\kappa (w)}{w (w - 1)} d ^ {2} w, \end{array}
$$

as well as

$$
\begin{array}{l} \frac {\partial}{\partial \varepsilon} \Big | _ {\varepsilon = 0} \mathcal {A} (g _ {\varepsilon}) \circ \gamma_ {\varepsilon \kappa} (\gamma_ {\varepsilon \kappa}) _ {z} = \left(\frac {\partial}{\partial \varepsilon} \Big | _ {\varepsilon = 0} \mathcal {A} (v _ {\varepsilon})\right) \circ g g ^ {\prime} - \frac {\partial}{\partial \varepsilon} \Big | _ {\varepsilon = 0} \mathcal {A} (\gamma_ {\varepsilon \kappa}) \\ \qquad = - \frac {2}{\pi} \iint_ {\mathbb {D}} \kappa (w) \left(\frac {g ^ {\prime} (w) ^ {2} g ^ {\prime} (z)}{(g (w) - g (z)) ^ {3}} - \frac {1}{(w - z) ^ {3}}\right) d ^ {2} w, \end{array}
$$

and

$$
\left. \frac {\partial}{\partial \varepsilon} \right| _ {\varepsilon = 0} \overline {{\mathcal {A} \left(g _ {\varepsilon}\right) \circ \gamma_ {\varepsilon \kappa} \left(\gamma_ {\varepsilon \kappa}\right) _ {z}}} = - \overline {{\frac {\partial}{\partial \bar {\varepsilon}} \Big | _ {\varepsilon = 0} \mathcal {A} \left(\gamma_ {\varepsilon \kappa}\right)}} = \frac {2}{\pi} \iint_ {\mathbb {D}} \frac {\kappa (w)}{(1 - w \bar {z}) ^ {3} w} d ^ {2} w.
$$

From here we get

$$
2 \pi \left. \frac {\partial}{\partial \varepsilon} \right| _ {\varepsilon = 0} \log | g _ {\varepsilon} ^ {\prime} (0) | ^ {2} = - 2 \iint_ {\mathbb {D}} \kappa (w) \left(\frac {g ^ {\prime} (w) ^ {2}}{g (w) ^ {2}} - \frac {1}{w ^ {2}}\right) d ^ {2} w = I _ {2},
$$

and

$$
\begin{array}{l} \frac {\partial}{\partial \varepsilon} \bigg | _ {\varepsilon = 0} \iint_ {\mathbb {D}} | \mathcal {A} (g _ {\varepsilon}) | ^ {2}   d ^ {2} z = \left. \frac {\partial}{\partial \varepsilon} \right| _ {\varepsilon = 0} \iint_ {\mathbb {D}} | \mathcal {A} (g _ {\varepsilon}) \circ \gamma_ {\varepsilon \kappa} (\gamma_ {\varepsilon \kappa}) _ {z} | ^ {2}   (1 - | \varepsilon \kappa | ^ {2}) d ^ {2} z \\ = - \frac {2}{\pi} \iint_ {\mathbb {D}} \iint_ {\mathbb {D}} \kappa (w) \left(\frac {g ^ {\prime} (w) ^ {2} g ^ {\prime} (z)}{(g (w) - g (z)) ^ {3}} - \frac {1}{(w - z) ^ {3}}\right) \overline {{\mathcal {A} (g) (z)}} d ^ {2} w d ^ {2} z \\ + \frac {2}{\pi} \iint_ {\mathbb {D}} \iint_ {\mathbb {D}} \frac {\kappa (w) \mathcal {A} (g) (z)}{w (1 - w \bar {z}) ^ {3}} d ^ {2} w d ^ {2} z = I _ {3} + I _ {4}. \end{array}
$$

Let $\log g'(z) = \sum_{n=0}^{\infty} a_n z^n$ be the power series expansion of $\log g'(z)$. Then $\mathcal{A}(g) = \sum_{n=1}^{\infty} na_n z^{n-1}$. Explicit computation gives

$$
\frac {2}{\pi} \iint_ {\mathbb {D}} \frac {\mathcal {A} (g) (z)}{w (1 - w \bar {z}) ^ {3}} d ^ {2} z = \sum_ {n = 1} ^ {\infty} n (n + 1) a _ {n} w ^ {n - 2} = \mathcal {A} (g) ^ {\prime} (w) + \frac {2}{w} \mathcal {A} (g) (w).
$$

Hence

$$
I _ {4} = \iint_ {\mathbb {D}} \kappa (w) \left(\mathcal {A} (g) ^ {\prime} (w) + \frac {2}{w} \mathcal {A} (g) (w)\right) d ^ {2} w.
$$

To compute the other terms, we define the following holomorphic function on $\mathbb{D}$,

$$
\begin{array}{l} h (w) = \frac {1}{\pi} \iint_ {\mathbb {D} ^ {*}} \frac {g ^ {\prime} (w) f ^ {\prime} (z)}{(g (w) - f (z)) ^ {2}} \overline {{\mathcal {A} (f) (z)}} d ^ {2} z \\ \qquad + \frac {1}{\pi} \iint_ {\mathbb {D}} \left(\frac {g ^ {\prime} (w) g ^ {\prime} (z)}{(g (w) - g (z)) ^ {2}} - \frac {1}{(w - z) ^ {2}}\right) \overline {{\mathcal {A} (g) (z)}} d ^ {2} z. \end{array}
$$

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

<!-- page 99 of 136 -->

90

2. KÄHLER POTENTIAL AND PERIOD MAPPING

Then it is easy to check that

$$
\begin{array}{c} \frac {\partial}{\partial \varepsilon} \Big | _ {\varepsilon = 0} \tilde {\mathsf {S}} (\gamma_ {\varepsilon}) = I _ {1} + I _ {2} + I _ {3} + I _ {4} \\ = \iint_ {\mathbb {D}} \kappa (w) \left(h ^ {\prime} (w) - \mathcal {A} (g) (w) h (w) - 2 \frac {g ^ {\prime} (w) ^ {2}}{g (w) ^ {2}} + \frac {2}{w ^ {2}} + \mathcal {A} (g) ^ {\prime} (w) + \frac {2}{w} \mathcal {A} (g) (w)\right) d ^ {2} w. \end{array}
$$

To finish the proof, we claim that

$$
h (w) = \mathcal {A} (g) (w) - 2 \frac {g ^ {\prime} (w)}{g (w)} + \frac {2}{w},
$$

which is going to be proved in the next lemma. With this equation for $h$, it is straightforward to compute that

$$
\begin{array}{l} \frac {\partial}{\partial \varepsilon} \bigg | _ {\varepsilon = 0} \tilde {\mathsf {S}} (\gamma_ {\varepsilon}) = \iint_ {\mathbb {D}} \left(2 \mathcal {A} (g) ^ {\prime} (w) - \mathcal {A} (g) (w) ^ {2}\right) \kappa (w) d ^ {2} w \\ \qquad = 2 \iint_ {\mathbb {D}} \mathcal {S} (g) (w) \kappa (w) d ^ {2} w = 2 \iint_ {\mathbb {D}} \mathcal {S} (\mathrm{g} _ {\nu}) (w) \mu (w) d ^ {2} w. \end{array}
$$

Returning back to the model $T(1) = L^{\infty}(\mathbb{D}^{*})_{1} / \sim$, we get the statement of the theorem.

LEMMA 3.6. In the model $T(1) \simeq L^{\infty}(\mathbb{D})_{1} / \sim$, let $\gamma = g^{-1} \circ f$ be the conformal welding corresponding to $\gamma \in \mathcal{T}_0(1)$. Then for $z \in \mathbb{D}$ the following identity holds


> **[ERRATUM 4-22]** (TT:4962–4968; Lean: `lemma_3_6`, Ch2/S3_Variations) Misprint; the kernel is K₁ of (f, g) (cf. TT:3949 and Remark 3.10).

$$
\begin{array}{l} \mathcal {A} (g) (z) - 2 \frac {g ^ {\prime} (z)}{g (z)} + \frac {2}{z} = \frac {1}{\pi} \iint_ {\mathbb {D} ^ {*}} \frac {g ^ {\prime} (z) f ^ {\prime} (w)}{(g (z) - f (w)) ^ {2}} \overline {{\mathcal {A} (f) (w)}} d ^ {2} w \\ \qquad + \frac {1}{\pi} \iint_ {\mathbb {D}} \left(\frac {g ^ {\prime} (z) g ^ {\prime} (w)}{(g (w) - g (w)) ^ {2}} - \frac {1}{(z - w) ^ {2}}\right) \overline {{\mathcal {A} (g) (w)}} d ^ {2} w. \end{array}
$$

PROOF. First we consider the case when  $\mathcal{A}(g)$  and  $\mathcal{A}(f)$  are smooth functions on  $S^{1}$ . Specifically, we assume that the Beltrami differential  $\mu$  corresponding to  $\pi(\gamma) \in T_{0}(1)$ , is smooth on C and  $\mu|_{S^{1}} = \mu_{\bar{z}}|_{S^{1}} = 0$ . Denote by  $h(z)$  the right-hand side of the identity of the lemma. Changing the variables of integration and using Stokes' theorem, we obtain

$$
\left| \begin{array}{c} h \circ g ^ {- 1} (g ^ {- 1}) ^ {\prime} (z) = - \frac {1}{\pi} \iint_ {\Omega^ {*}} \frac {\overline {{\mathcal {A} (f ^ {- 1}) (w)}}}{(z - w) ^ {2}} d ^ {2} w - \frac {1}{\pi} \iint_ {\Omega} \frac {\overline {{\mathcal {A} (g ^ {- 1}) (w)}}}{(z - w) ^ {2}} d ^ {2} w \\ = \frac {1}{2 \pi i} \oint_ {\mathcal {C}} \frac {1}{(z - w)} \left(\overline {{\mathcal {A} (g ^ {- 1}) (w)}} - \overline {{\mathcal {A} (f ^ {- 1}) (w)}}\right) d \bar {w}, \end{array} \right|
$$

where $\Omega = g(\mathbb{D}),\Omega^{*} = f(\mathbb{D}^{*})$ and $\mathcal{C} = g(S^1)$. Next, consider the relation $\tilde{\gamma}\circ g^{-1} = f^{-1}$, where $\tilde{\gamma} = \gamma^{-1}$, and differentiate it twice with respect to $z$. Since $\tilde{\gamma}_{\bar{z}}$ vanishes on $S^1$, we get the following relations on $\mathcal{C}$,

$$
\frac {\tilde {\gamma} _ {z}}{\tilde {\gamma}} \circ g ^ {- 1} (g ^ {- 1}) _ {z} = \frac {(f ^ {- 1}) _ {z}}{f ^ {- 1}},
$$

$$
\mathcal {A} (\tilde {\gamma}) \circ g ^ {- 1} (g ^ {- 1}) _ {z} = \mathcal {A} (f ^ {- 1}) - \mathcal {A} (g ^ {- 1}).
$$

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

<!-- page 100 of 136 -->

3. VARIATIONS OF THE FUNCTIONS $S_{1}$ AND $S_{2}$

91

Hence

$$
\begin{array}{r l} h \circ g ^ {- 1} (g ^ {- 1}) ^ {\prime} (z) & = - \frac {1}{2 \pi i} \oint_ {\mathcal {C}} \frac {1}{(z - w)} \overline {{(\mathcal {A} (\tilde {\gamma}) \circ g ^ {- 1}) (w) (g ^ {- 1}) _ {w} (w)}} d \bar {w} \\ & = - \frac {1}{2 \pi i} \oint_ {S ^ {1}} \frac {1}{z - g (w)} \overline {{\mathcal {A} (\tilde {\gamma}) (w)}} d \bar {w}. \end{array}
$$

On the other hand, since $j \circ \tilde{\gamma} = \tilde{\gamma} \circ j$, where $j$ is the inversion $z \mapsto \frac{1}{z}$, we have

$$
\overline {{\mathcal {A} (\tilde {\gamma})}} = \mathcal {A} (\tilde {\gamma}) \circ j j _ {\bar {z}} - 2 \frac {\tilde {\gamma} _ {z}}{\tilde {\gamma}} \circ j j _ {\bar {z}} + \overline {{\mathcal {A} (\bar {j})}}.
$$

Hence

$$
\begin{array}{c} h \circ g ^ {- 1} (g ^ {- 1}) ^ {\prime} (z) = \frac {1}{2 \pi i} \oint_ {S ^ {1}} \frac {1}{z - g (w)} \left(\mathcal {A} (\tilde {\gamma}) \left(\frac {1}{\bar {w}}\right) \frac {1}{\bar {w} ^ {2}} - 2 \frac {\tilde {\gamma} _ {w}}{\tilde {\gamma}} \left(\frac {1}{\bar {w}}\right) \frac {1}{\bar {w} ^ {2}} + \frac {2}{\bar {w}}\right) d \bar {w} \\ = - \frac {1}{2 \pi i} \oint_ {S ^ {1}} \frac {1}{z - g (w)} \left(\mathcal {A} (\tilde {\gamma}) (w) - 2 \frac {\tilde {\gamma} _ {w} (w)}{\tilde {\gamma} (w)} + \frac {2}{w}\right) d w \\ = \frac {1}{2 \pi i} \oint_ {\mathcal {C}} \frac {1}{(z - w)} \left(\mathcal {A} (g ^ {- 1}) (w) - \mathcal {A} (f ^ {- 1}) (w) + 2 \frac {(f ^ {- 1}) _ {w} (w)}{f ^ {- 1} (w)} - 2 \frac {(g ^ {- 1}) _ {w} (w)}{g ^ {- 1} (w)}\right) d w. \end{array}
$$

The functions

$$
\mathcal {A} (f ^ {- 1}) (z) - 2 \frac {(f ^ {- 1}) _ {z} (z)}{f ^ {- 1} (z)} + \frac {2}{z} \quad \text {and} \quad \mathcal {A} (g ^ {- 1}) (z) - 2 \frac {(g ^ {- 1}) _ {z} (z)}{g ^ {- 1} (z)} + \frac {2}{z}
$$

are holomorphic on $\Omega^{*} = f(\mathbb{D}^{*})$ and $\Omega = g(\mathbb{D})$ respectively and due to the normalization of $f$,

$$
\mathcal {A} (f ^ {- 1}) (z) - 2 \frac {(f ^ {- 1}) _ {z} (z)}{f ^ {- 1} (z)} + \frac {2}{z} = O \left(\frac {1}{z ^ {2}}\right) \quad \text {as} \quad z \to \infty .
$$

Thus we have by Cauchy formula

$$
h \circ g ^ {- 1} (g ^ {- 1}) ^ {\prime} (z) = - \left(\mathcal {A} (g ^ {- 1}) (z) - 2 \frac {(g ^ {- 1}) ^ {\prime} (z)}{g ^ {- 1} (z)} + \frac {2}{z}\right)
$$

or equivalently,

$$
h (z) = \mathcal {A} (g) (z) - 2 \frac {g ^ {\prime} (z)}{g (z)} + \frac {2}{z}.
$$

For a general point $\gamma = g^{-1} \circ f$ in $\mathcal{T}_0(1)$, we let $f_n = r_n^{-1} \circ f \circ r_n$, where $r_n$ is the dilation $z \mapsto \frac{n+1}{n} z$. Since $f_n$ is a normalized univalent function on $|z| > \frac{n}{n+1}$, corresponding $\gamma_n^{-1} = g_n^{-1} \circ f_n \in \mathcal{T}_0(1)$ satisfies the assumptions made in the beginning of the proof. Since $\mathcal{A}(f) \in A_2^1(\mathbb{D}^*)$, we see that

$$
\begin{array}{l} \left\| \mathcal {A} (\iota \circ f _ {n} \circ \iota) - \mathcal {A} (\iota \circ f \circ \iota) \right\| _ {A _ {2} ^ {1} (\mathbb {D})} \\ = \left\| \left(\mathcal {A} (f _ {n}) - 2 \frac {f _ {n} ^ {\prime}}{f _ {n}} + \frac {2}{z}\right) - \left(\mathcal {A} (f) - 2 \frac {f ^ {\prime}}{f} + \frac {2}{z}\right) \right\| _ {A _ {2} ^ {1} (\mathbb {D} ^ {*})} \to 0 \quad \text {as} \quad n \to \infty . \end{array}
$$

By Corollary A.4 and Corollary A.6 in Appendix A we also have

$$
\lim _ {n \to \infty} \| \mathcal {A} (g _ {n}) - \mathcal {A} (g) \| _ {A _ {2} ^ {1} (\mathbb {D})} = 0
$$

and

$$
\lim _ {n \to \infty} \left\| \left(\mathcal {A} (g _ {n}) - 2 \frac {g _ {n} ^ {\prime}}{g _ {n}} + \frac {2}{z}\right) - \left(\mathcal {A} (g) - 2 \frac {g ^ {\prime}}{g} + \frac {2}{z}\right) \right\| _ {A _ {2} ^ {1} (\mathbb {D})} = 0.
$$

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

<!-- page 101 of 136 -->

92

2. KÄHLER POTENTIAL AND PERIOD MAPPING

In particular, since convergence in $A_2^1 (\mathbb{D})$ implies convergence in $A_{\infty}^{1}(\mathbb{D})$, we get

$$
\varliminf_ {n \to \infty} \left(\mathcal {A} (g _ {n}) (z) - 2 \frac {g _ {n} ^ {\prime}}{g _ {n}} (z) + \frac {2}{z}\right) = \mathcal {A} (g) (z) - 2 \frac {g ^ {\prime}}{g} (z) + \frac {2}{z},
$$

uniformly on compact subsets of $\mathbb{D}$. Since we have already shown that

$$
h _ {n} (z) = \mathcal {A} (g _ {n}) (z) - 2 \frac {g _ {n} ^ {\prime}}{g _ {n}} (z) + \frac {2}{z},
$$

to finish the proof of the lemma we need to verify that $\lim_{n\to \infty}h_n(z) = h(z)$ uniformly on compact subsets of $\mathbb{D}$.

We denote by $K_{1}[n]$ and $K_{2}[n]$ the operators associated with the disjoint pair of univalent functions $(g_n, f_n)$, and by $K_{1}$ and $K_{2}$ — the operators associated with the pair $(g, f)$. Then

$$
\begin{array}{c} h _ {n} (z) - h (z) = - \Big (K _ {1} [ n ] \overline {{\mathcal {A} (g _ {n})}} \Big) (z) + \Big (K _ {1} \overline {{\mathcal {A} (g)}} \Big) (z) \\ \qquad + \Big (K _ {2} [ n ] \overline {{\mathcal {A} (f _ {n})}} \Big) (z) - \Big (K _ {2} \overline {{\mathcal {A} (f)}} \Big) (z). \end{array}
$$

Now using Theorem B.1 from Appendix B, and the fact that the inverse map is continuous on $T_0(1)$, we get that

$$
\lim _ {n \to \infty} \| K _ {1} [ n ] - K _ {1} \| = 0,
$$

where $\| \cdot \|$ stands for the norm of the Banach space $\mathcal{B}(\overline{A_2^1(\mathbb{D})}, A_2^1(\mathbb{D}))$. Since $\| K_1[n] \| \leq 1$, we have

$$
\begin{array}{c} \Big \| K _ {1} [ n ] \overline {{\mathcal {A} (g _ {n})}} - K _ {1} \overline {{\mathcal {A} (g)}} \Big \| _ {A _ {2} ^ {1} (\mathbb {D})} \\ \leq \Big \| K _ {1} [ n ] \big (\overline {{\mathcal {A} (g _ {n}) - \mathcal {A} (g)}} \big) \Big \| _ {A _ {2} ^ {1} (\mathbb {D})} + \Big \| \big (K _ {1} [ n ] - K _ {1} \big) \overline {{\mathcal {A} (g)}} \Big \| _ {A _ {2} ^ {1} (\mathbb {D})} \\ \leq \| \mathcal {A} (g _ {n}) - \mathcal {A} (g) \| _ {A _ {2} ^ {1} (\mathbb {D})} + \| K _ {1} [ n ] - K _ {1} \| \| \mathcal {A} (g) \| _ {A _ {2} ^ {1} (\mathbb {D})}, \end{array}
$$

which tends to 0 as $n\to \infty$ . Consequently,

$$
\lim _ {n \to \infty} (K _ {1} [ n ] \overline {{\mathcal {A} (g _ {n})}}) (z) = (K _ {1} \overline {{\mathcal {A} (g)}}) (z),
$$

uniformly on compact subsets of $\mathbb{D}$.

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

To prove the convergence of the other term in $h_n(z) - h(z)$, we let $\mathfrak{g}_n = r_n \circ g_n$ and $\mathfrak{f}_n = r_n \circ f_n = f \circ r_n$. Let $\Omega_n^* = \mathfrak{f}_n(\mathbb{D}^*) = f(\{|z| > \frac{n+1}{n}\})$. Since $\Omega_n^* \subseteq \Omega_{n+1}^*$, the sequence of domains $\Omega_n = \mathfrak{g}_n(\mathbb{D})$ is a decreasing sequence that contains 0 and $\bigcap \mathfrak{g}_n(\mathbb{D}) = g(\mathbb{D}) = \Omega$. By Caratheodory kernel theorem (see, e.g., [Pom92]), the sequence of univalent functions $\mathfrak{g}_n : \mathbb{D} \to \mathbb{C}$ converges uniformly on compact sets to the univalent function $g : \mathbb{D} \to \mathbb{C}$. By Weierstrass theorem, $\lim_{n \to \infty} \mathfrak{g}_n'(z) = g'(z)$, uniformly on compact subsets of $\mathbb{D}$. Using that the operator $K_2$ is unaffected by a simultaneous post-composition of $f$ and $g$ with $\alpha \in \mathrm{PSL}(2, \mathbb{C})$ and that $\mathcal{A}(\mathfrak{f}_n) = \mathcal{A}(r_n \circ f_n) = \mathcal{A}(f_n)$, we have

$$
\begin{array}{c} \left(K _ {2} [ n ] \overline {{\mathcal {A} (f _ {n})}}\right) (z) - \left(K _ {2} \overline {{\mathcal {A} (f)}}\right) (z) \\ = \frac {1}{\pi} \iint_ {\mathbb {D} ^ {*}} \frac {\mathfrak {g} _ {n} ^ {\prime} (z) \mathfrak {f} _ {n} ^ {\prime} (w)}{(\mathfrak {g} _ {n} (z) - \mathfrak {f} _ {n} (w)) ^ {2}} \overline {{\mathcal {A} (\mathfrak {f} _ {\mathfrak {n}}) (w)}} d ^ {2} w - \iint_ {\mathbb {D} ^ {*}} \frac {g ^ {\prime} (z) f ^ {\prime} (w)}{(g (z) - f (w)) ^ {2}} \overline {{\mathcal {A} (f) (w)}} d ^ {2} w \\ = u _ {n} (\mathfrak {g} _ {n} (z)) \mathfrak {g} _ {n} ^ {\prime} (z) - u (g (z)) g ^ {\prime} (z). \end{array}
$$

<!-- page 102 of 136 -->

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

3. VARIATIONS OF THE FUNCTIONS $S_{1}$ AND $S_{2}$

93

Here for $z\in \Omega_n = \mathfrak{g}_n(\mathbb{D})$ we set

$$
u _ {n} (z) = \frac {1}{\pi} \iint_ {\mathbb {D} ^ {*}} \frac {\mathfrak {f} _ {n} ^ {\prime} (w)}{(z - \mathfrak {f} _ {n} (w)) ^ {2}} \overline {{\mathcal {A} (\mathfrak {f} _ {\mathfrak {n}}) (w)}} d ^ {2} w = - \frac {1}{\pi} \iint_ {\Omega_ {n} ^ {*}} \overline {{\frac {\mathcal {A} (\mathfrak {f} _ {n} ^ {- 1}) (w)}{(z - w) ^ {2}}}} d ^ {2} w,
$$

and for $z\in \Omega = g(\mathbb{D})$

$$
u (z) = \frac {1}{\pi} \iint_ {\mathbb {D}} \frac {f ^ {\prime} (w)}{(z - f (w)) ^ {2}} \overline {{\mathcal {A} (f) (w)}} d ^ {2} w = - \frac {1}{\pi} \iint_ {\Omega^ {*}} \overline {{\frac {\mathcal {A} (f ^ {- 1}) (w)}{(z - w) ^ {2}}}} d ^ {2} w.
$$

Let $\tilde{u}_n = u_n|_\Omega$. Using $\mathcal{A}(\mathfrak{f}_n^{-1}) = \mathcal{A}(r_n^{-1} \circ f^{-1}) = \mathcal{A}(f^{-1})$ and $\Omega_n^* \subset \Omega^*$, we get

$$
\tilde {u} _ {n} (z) - u (z) = \frac {1}{\pi} \iint_ {\Omega^ {*} \backslash \Omega_ {n} ^ {*}} \overline {{\frac {\mathcal {A} (f ^ {- 1}) (w)}{(z - w) ^ {2}}}} d ^ {2} w.
$$

Since Hilbert transform is an isometry, we obtain

$$
\begin{array}{c} \| \tilde {u} _ {n} \circ g   g ^ {\prime} - u \circ g   g ^ {\prime} \| _ {A _ {2} ^ {1} (\mathbb {D})} ^ {2} = \iint_ {\mathbb {D}} | \tilde {u} _ {n} (g (z)) g ^ {\prime} (z) - u (g (z)) g ^ {\prime} (z) | ^ {2}   d ^ {2} z \\ = \iint_ {\Omega} | \tilde {u} _ {n} (z) - u (z) | ^ {2} d ^ {2} z \leq \iint_ {\Omega^ {*} \setminus \Omega_ {n} ^ {*}} | \mathcal {A} (f ^ {- 1}) (z) | ^ {2} d ^ {2} z = \iint_ {1 <   | z | <   \frac {n + 1}{n}} | \mathcal {A} (f) (z) | ^ {2} d ^ {2} z. \end{array}
$$

Since $\mathcal{A}(f)\in A_2^1 (\mathbb{D}^*)$, we get

$$
\lim _ {n \to \infty} \| \tilde {u} _ {n} \circ g   g ^ {\prime} - u \circ g   g ^ {\prime} \| _ {A _ {2} ^ {1} (\mathbb {D})} = 0,
$$

and, consequently, $\lim_{n\to \infty}\tilde{u}_n(z) = u(z)$, uniformly on compact subsets of $\Omega$. For every compact subset $E\subset \mathbb{D}$, $\mathfrak{g}_n(E)\subset \Omega$ for $n$ sufficiently large, and it follows that

$$
\lim _ {n \to \infty} u _ {n} (\mathfrak {g} _ {n} (z)) \mathfrak {g} _ {n} ^ {\prime} (z) = u (g (z)) g ^ {\prime} (z),
$$

uniformly on $E$.

□

COROLLARY 3.7. On $T_0(1)$,

$$
\partial \tilde {\mathsf {S}} _ {1} = 2 \vartheta .
$$

THEOREM 3.8. The functions $S_1, \tilde{S}_1, S_2$ on $T_0(1)$ satisfy the following relations,

$$
\mathrm{S} _ {2} = - \frac {1}{1 2 \pi} \mathrm{S} _ {1} = - \frac {1}{1 2 \pi} \tilde {\mathrm{S}} _ {1}.
$$

In particular, in Bers coordinates $\varepsilon_{\mu}$ on the chart $V_{\nu}$ at $[\nu] \in T_0(1)$,

$$
\frac {\partial \mathsf {S} _ {1}}{\partial \varepsilon_ {\mu}} ([ \nu ]) = 2 \iint_ {\mathbb {D} ^ {*}} \mathcal {S} (\mathrm{g} _ {\nu}) (z) \mu (z) d ^ {2} z,
$$

where $w_{\nu} = \mathrm{g}_{\nu}^{-1}\circ \mathrm{f}^{\nu}$ is the conformal welding corresponding to $[\nu ]\in T_0(1)$.

PROOF. Since $S_{2}(0) = \tilde{S}_{1}(0) = 0$, Theorems 3.1 and 3.5 immediately give

$$
S _ {2} = - \frac {1}{1 2 \pi} \tilde {S} _ {1}.
$$

Since the function $S_{2}$ is symmetric,

$$
\mathsf {S} _ {2} ([ \mu ]) = \mathsf {S} _ {2} ([ \mu ] ^ {- 1}),
$$

<!-- page 103 of 136 -->

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026for download from IP 130.34.46.51.

94

2. KÄHLER POTENTIAL AND PERIOD MAPPING

the function $\tilde{S}_1$ is also symmetric, so that $\tilde{S}_1 = S_1$.

□

COROLLARY 3.9. On $T_0(1)$,

$$
\partial \mathsf {S} _ {1} = 2 \vartheta .
$$

REMARK 3.10. Returning to the model $T(1) = L^{\infty}(\mathbb{D}^{*}) / \sim$, let $\gamma = g^{-1} \circ f \in \mathcal{T}_0(1)$. Introducing the operator $\mathbf{K}: \overline{A_2^1(\mathbb{D})} \oplus \overline{A_2^1(\mathbb{D}^*)} \to A_2^1(\mathbb{D}) \oplus A_2^1(\mathbb{D}^*)$,

$$
\mathbf {K} = \left( \begin{array}{c c} K _ {1} & K _ {2} \\ K _ {3} & K _ {4} \end{array} \right),
$$

and the vectors

$$
\mathbf {u} = \binom{u _ {1}}{u _ {2}}, \mathbf {v} = \binom{v _ {1}}{v _ {2}} \in A _ {2} ^ {1} (\mathbb {D}) \oplus A _ {2} ^ {1} (\mathbb {D} ^ {*}),
$$

where $u_{1} = \mathcal{A}(\imath \circ f\circ \imath)\circ \imath \imath^{\prime},u_{2} = -\mathcal{A}(\imath \circ g\circ \imath)\circ \imath \imath^{\prime}$ and $v_{1} = \mathcal{A}(f),v_{2} = -\mathcal{A}(g)$. Applying Lemma 3.6 to $\gamma$ and $\gamma^{-1}$ and using generalized Grunsky equality, we can succinctly rewrite the two identities as a single equation

$$
\mathbf {K} \bar {\mathbf {u}} = - \mathbf {v}.
$$

Indeed, Lemma 3.6 applied to $\gamma$ and $\gamma^{-1}$ gives

$$
K _ {3} \bar {u} _ {1} + K _ {4} \bar {u} _ {2} = - v _ {2} \quad \text {and} \quad K _ {1} \bar {v} _ {1} + K _ {2} \bar {v} _ {2} = - u _ {1},
$$

and from generalized Grunsky equality it follows that the functions

$$
w _ {1} (z) = \left(\log \frac {f (z)}{z}\right) ^ {\prime} = - \sum_ {n = 1} ^ {\infty} n b _ {- n, 0} z ^ {n - 1}
$$

and

$$
w _ {2} (z) = - \left(\log \frac {g (z)}{z}\right) ^ {\prime} = - \sum_ {n = 1} ^ {\infty} n b _ {n, 0} z ^ {- n - 1}
$$

satisfy the equations

$$
K _ {1} \bar {w} _ {1} + K _ {2} \bar {w} _ {2} = w _ {1} \quad \text {and} \quad K _ {3} \bar {w} _ {1} + K _ {4} \bar {w} _ {2} = w _ {2}.
$$

Since $u_{1} = v_{1} - 2w_{1}$ and $u_{2} = v_{2} - 2w_{2}$, we get the equation $\mathbf{K}\bar{\mathbf{u}} = -\mathbf{v}$. Similarly, we get the equation $\mathbf{K}\bar{\mathbf{v}} = -\mathbf{u}$.

REMARK 3.11. For $C^3$ curves the result of Theorem 3.5 was obtained by Schiffer and Hawley in [SH62]. They have used a completely different approach which can not be generalized to quasi-circles for $T_0(1)$.

The equality  $S_{2} = -\frac{1}{12\pi}S_{1}$  can be also interpreted as a surgery type formula for determinants of elliptic operators (see [BFK92, HZ99]). Namely, let  $\Delta_{\varphi}$  be the Laplace operator of the conformal metric  $e^{2\varphi(z)}|dz|^{2}$  on D with Dirichlet boundary condition. Its zeta-function regularized determinant  $\det\Delta_{\varphi}$  is given by the Polyakov-Alvarez formula

$$
\log \det \Delta_ {\varphi} = - \frac {1}{3 \pi} \iint_ {\mathbb {D}} | \varphi_ {z} | ^ {2} d ^ {2} z - \frac {1}{6 \pi} \oint_ {S ^ {1}} \varphi (e ^ {i \theta}) d \theta + \log \det \Delta_ {0}.\tag{3.3}
$$

Now let $\gamma = \mathrm{g}^{-1} \circ \mathrm{f} \in T_0(1)$ and set, as before, $\tilde{\mathrm{g}} = \imath \circ \mathrm{g} \circ \imath$, $\tilde{\mathrm{f}} = \imath \circ \mathrm{f} \circ \imath$. The metric $|\tilde{\mathrm{g}}'(z)|^2 |dz|^2$ is a pull-back of the Euclidean metric $|dw|^2$ on $\tilde{\Omega} = \tilde{\mathrm{g}}(\mathbb{D})$ by the conformal mapping $\tilde{\mathrm{g}}$. Assume that $\phi(z) = \frac{1}{2} \log |\tilde{\mathrm{g}}'(z)|^2$ is of $C^1$ class on $S^1$, and

<!-- page 104 of 136 -->

4. WEIL-PETERSSON POTENTIAL

95

denote by $\Delta_{\tilde{\Omega}}$ the Laplace operator of the Euclidean metric on $\tilde{\Omega}$ with Dirichlet boundary condition. From (3.3) we immediately get

$$
\left| \log \det \Delta_ {\tilde {\Omega}} = - \frac {1}{1 2 \pi} \iint_ {\mathbb {D}} | \mathcal {A} (\tilde {\mathrm{g}}) | ^ {2} d ^ {2} z - \frac {1}{3} \log | \tilde {\mathrm{g}} ^ {\prime} (0) | + \log \det \Delta_ {\mathbb {D}}. \right|
$$

Now consider the metric $|\tilde{\mathrm{f}}'(\frac{1}{z})|^2 |dz|^2$ on $\mathbb{D}$ — a pull-back of the flat metric

$$
d s ^ {2} = \frac {| d w | ^ {2}}{| \tilde {\mathrm{f}} ^ {- 1} (w) | ^ {4}}
$$

on $\tilde{\Omega}^{*} = \tilde{\mathrm{f}}(\mathbb{D}^{*})$ by the conformal mapping $\tilde{\mathrm{f}}\circ \imath$. Denoting by $\Delta_{\tilde{\Omega}^*}$ the Laplace operator of the metric $ds^2$ on $\tilde{\Omega}^*$ with Dirichlet boundary condition, we get from (3.3),

$$
\log \det \Delta_ {\tilde {\Omega} ^ {*}} = - \frac {1}{1 2 \pi} \iint_ {\mathbb {D} ^ {*}} | \mathcal {A} (\tilde {\mathrm{f}}) | ^ {2} d ^ {2} z + \log \det \Delta_ {\mathbb {D} ^ {*}},
$$

where we again assumed that $\varphi(z) = \frac{1}{2} \log |\tilde{\mathbf{f}}'(\frac{1}{z})|^2$ is of $C^1$ class on $S^1$. Here $\Delta_{\mathbb{D}^*}$ is the Laplace operator of the metric $\frac{|dw|^2}{|w|^4}$ on $\mathbb{D}^*$. Note that the metric $ds^2$ is regular at $\infty$, so that $\Delta_{\tilde{\Omega}^*}$ is an elliptic operator (cf. [HZ99]). The following result now follows from Theorem 3.8 and the symmetry property $S_1([\mu]) = S_1([\mu^{-1}])$.

COROLLARY 3.12. Let $\gamma = \mathrm{g}^{-1} \circ \mathrm{f} \in T_0(1)$ be of $C^3$ class on $S^1$. Then for $\mathcal{C} = \mathrm{f}(S^1)$,

$$
\mathrm{Det} _ {F} (\mathcal {C}) = \frac {\det \Delta_ {\tilde {\Omega}} \det \Delta_ {\tilde {\Omega} ^ {*}}}{\det \Delta_ {\mathbb {D}} \det \Delta_ {\mathbb {D} ^ {*}}}.
$$

REMARK 3.13. The statement of Corollary 3.12 can be interpreted as a surgery type formula in the spirit of [BFK92] for the Laplace operator of a conformal metric on the Riemann sphere $\mathbb{P}^1$, which is the Euclidean metric on the interior domain $\tilde{\Omega} = \iota (\Omega^{*})$ and is the metric $ds^{2} = \frac{|dw|^{2}}{|\tilde{\mathfrak{f}}^{-1}(w)|^{4}}$ on the exterior domain $\tilde{\Omega}^{*} = \iota (\Omega)$ (and thus is continuous on $\mathbb{P}^1$). The Fredholm determinant $\mathrm{Det}_F(\mathcal{C})$ is the inverse of the determinant of the Neumann jump operator which corresponds to cutting of $\mathbb{P}^1$ along the contour $\mathcal{C}$ and considering Dirichlet boundary conditions for interior and exterior Laplace operators (cf. [HZ99]).

## 4. Weil-Petersson potential

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

4.1. Weil-Petersson potential on  $T_{0}(1)$ . As in the case of finite dimensional Teichmüller spaces [TT03], it follows from the results of the previous section that the function  $S_{1}$  is a potential for the Weil-Petersson metric on  $T_{0}(1)$ . For the convenience of the reader, here we give the details.

THEOREM 4.1. In terms of the Bers coordinates on the chart $V_{\kappa}$ at $\kappa \in T_0(1)$,

$$
\frac {\partial^ {2} \mathsf {S} _ {1}}{\partial \varepsilon_ {\mu} \bar {\varepsilon} _ {\nu}} ([ \kappa ]) = \iint_ {\mathbb {D} ^ {*}} \mu (z) \overline {{\nu (z)}} \rho (z) d ^ {2} z.
$$

PROOF. We have

$$
\frac {\partial^ {2} \mathsf {S} _ {1}}{\partial \varepsilon_ {\mu} \bar {\varepsilon} _ {\nu}} ([ \kappa ]) = \left. \frac {\partial}{\partial \bar {\varepsilon}} \right| _ {\varepsilon = 0} \frac {\partial \mathsf {S} _ {1}}{\partial \varepsilon_ {\mu}} ([ \varepsilon \nu * \kappa ]).
$$

<!-- page 105 of 136 -->

96

2. KÄHLER POTENTIAL AND PERIOD MAPPING

Using Theorem 3.8 and the fact that at the point $\varepsilon \nu * \kappa \in T_0(1)$ the vector field $\frac{\partial}{\partial\varepsilon_{\mu}}$ on the chart $V_{\kappa}$ is represented by $P(R(\mu, \varepsilon \nu)) \in H^{-1,1}(\mathbb{D}^*)$ on the chart $V_{\varepsilon \nu * \kappa}$ (see Section 2.3 in Chapter 1), we get


> **[IMPLICIT HYPOTHESIS 4-6]** (5318–5334; Lean: `eq_4_1`, `thm_4_1_variation`, `schwarzianDz`, S4_WPPotential) The memoir uses the ∂_z Schwarzian for q.c. maps without saying so.

$$
\begin{array}{r l} & {\frac {\partial \mathsf {S} _ {1}}{\partial \varepsilon_ {\mu}} (\varepsilon \nu * \kappa) = 2 \iint_ {\mathbb {D} ^ {*}} \mathcal {S} (g _ {\varepsilon \nu * \kappa}) P (R (\mu , \varepsilon \nu)) d ^ {2} z} \\ & {\qquad = 2 \iint_ {\mathbb {D} ^ {*}} \left(\mathcal {S} (g _ {\varepsilon}) \circ w _ {\varepsilon \nu} (w _ {\varepsilon \nu}) _ {z} ^ {2}\right) Q (R (\mu , \varepsilon \nu)) (1 - | \varepsilon \nu | ^ {2}) d ^ {2} z,} \end{array}
$$

where $g_{\varepsilon}^{-1}\circ f^{\varepsilon} = w_{\varepsilon \nu}\circ w_{\kappa},v_{\varepsilon} = f^{\varepsilon}\circ f^{-1}$, and $Q(R(\mu ,\varepsilon \nu))$ was defined in Section 7.1 in Chapter 1. Since $g_{\varepsilon}\circ w_{\varepsilon \nu} = v_{\varepsilon}\circ g$, we have

$$
\mathcal {S} (g _ {\varepsilon}) \circ w _ {\varepsilon \nu} (w _ {\varepsilon \nu}) _ {z} ^ {2} + \mathcal {S} (w _ {\varepsilon \nu}) = \mathcal {S} (v _ {\varepsilon}) \circ g (g ^ {\prime}) ^ {2} + \mathcal {S} (g),\tag{4.1}
$$

and it follows from the standard variational formula that


> **[IMPLICIT HYPOTHESIS 4-7]** (5330–5334; Lean: `thm_4_1_variation`, S4_WPPotential) Implicit: ε ↦ 𝒮_dz(v_ε)∘g·g'² is holomorphic in ε. It is, because v_ε has Beltrami coefficient ε·(ν pushed by g), which is linear in ε. Also implicit: C³ regularity of w_{εν} (W-REG model A). Sign cross-checked against the 𝕌 analogue varPhi''' = −(6/π)∫μ̄/(ū−z)⁴.

$$
\left. \frac {\partial}{\partial \bar {\varepsilon}} \right| _ {\varepsilon = 0} \mathcal {S} (g _ {\varepsilon}) \circ w _ {\varepsilon \nu} (w _ {\varepsilon \nu}) _ {z} ^ {2} = \frac {6}{\pi} \iint_ {\mathbb {D} ^ {*}} \frac {\overline {{\nu (w)}}}{(1 - \bar {w} z) ^ {4}} d ^ {2} w.
$$

Since according to Theorem 7.4 in Chapter 1

$$
\left. \frac {\partial}{\partial \bar {\varepsilon}} \right| _ {\varepsilon = 0} Q (R (\mu , \varepsilon \nu))
$$

is an infinitesimally trivial Beltrami differential, we have

$$
\frac {\partial^ {2}}{\partial \varepsilon_ {\mu} \bar {\varepsilon} _ {\nu}} S _ {1} ([ \kappa ]) = \frac {1 2}{\pi} \iint_ {\mathbb {D} ^ {*}} \iint_ {\mathbb {D} ^ {*}} \frac {\mu (z) \overline {{\nu (w)}}}{(1 - \bar {w} z) ^ {4}} d ^ {2} w d ^ {2} z = \iint_ {\mathbb {D} ^ {*}} \mu (z) \overline {{\nu (z)}} \rho (z) d ^ {2} z.
$$

COROLLARY 4.2. On $T_0(1)$,

$$
\partial \bar {\partial} \mathsf {S} _ {1} = - 2 i \omega_ {W P},
$$

where $\omega_{WP}$ is the symplectic form of the Weil-Petersson metric. In other words, $S_{1}$ is a potential of the Weil-Petersson metric on $T_0(1)$.

REMARK 4.3. It follows from Corollary 2.16 and Theorem 3.8 that on $T_0(1)$,

$$
\partial \bar {\partial} \log \det N _ {\Omega} = \frac {i}{6 \pi} \omega_ {W P}.
$$

In the spirit of the last remark in Section 8 of Chapter 1, this result should be compared to the local index theorem for families of $\bar{\partial}$-operators on compact Riemann surfaces,

$$
\partial \bar {\partial} \log \det \Delta_ {0} - \partial \bar {\partial} \log \det N _ {1} = - \frac {i}{6 \pi} \omega_ {W P},
$$

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026for download from IP 130.34.46.51.

where $N_{1}$ is the period matrix of 1-forms on a compact Riemann surface $X$ and $\Delta_0$ is the Laplace operator of the hyperbolic metric on $X$ (see, e.g., [ZT87]).

REMARK 4.4. It follows from Corollary 3.9 that on $T_0(1)$,

$$
\partial \boldsymbol {\vartheta} = 0.
$$


> **[ERRATUM 4-1]** (5376; Lean: `remark_4_4`, `lieTheta`, S4_WPPotential) Misprint: the derivative defining `L_ν` is ∂/∂ε along `εν`. The subscript μ is wrong; ν is the direction.

<!-- page 106 of 136 -->


> **[IMPLICIT HYPOTHESIS 4-2]** (5378; Lean: `remark_4_4` (first clause), S4_WPPotential) Dropping the term uses the 𝔻*-analogue of Lemma 1.12 (PV of ν/(w−z)⁴ = 0). The remaining integrand is O(\|w−z\|⁻⁴), so the integral exists only as a PV, which the memoir leaves implicit.

5. THE PERIOD MAPPING


> **[IMPLICIT HYPOTHESIS 4-3]** (5380–5390; Lean: `remark_4_4` (second clause), S4_WPPotential) The cancellation swaps the order of a double integral whose kernel is not absolutely integrable (same trap as the eq_7_4 W1 wall). It needs a PV/Fubini justification the memoir omits.

97

Here is a direct proof of this result, following our work [TT03]. From equation (4.1), we have at $[\kappa] \in T_0(1)$,

$$
\begin{array}{l} (L _ {\nu} \vartheta) (z) = \left. \frac {\partial}{\partial \varepsilon_ {\mu}} \right| _ {\varepsilon = 0} \mathcal {S} (g _ {\varepsilon}) \circ w _ {\varepsilon \nu} (w _ {\varepsilon \nu}) _ {z} ^ {2} (z) \\ \qquad = - \frac {1 2}{\pi} \iint_ {\mathbb {D} ^ {*}} \nu (w) \left(\frac {g ^ {\prime} (w) ^ {2} g ^ {\prime} (z) ^ {2}}{(g (w) - g (z)) ^ {4}} - \frac {1}{(w - z) ^ {4}}\right) d ^ {2} w \\ \qquad = - \frac {1 2}{\pi} \iint_ {\mathbb {D} ^ {*}} \nu (w) \frac {g ^ {\prime} (w) ^ {2} g ^ {\prime} (z) ^ {2}}{(g (w) - g (z)) ^ {4}} d ^ {2} w. \end{array}
$$


> **[ERRATUM G-1]** (5387; Lean: `remark_4_4` (clause 1), Ch2 S4_WPPotential) ∂_ε S(w_εν) = ∂³ẇ = −(6/π) PV∫ν(w)/(w−z)⁴ (installed `qcv_ahVar_iter3`); the factor 12 is copied from Thm 4.1, where ∂S₁ = 2ϑ supplies the 2. Clause 2 (∂ϑ = 0) unaffected. Found by 下属5.

Hence,

$$
\begin{array}{r l} & {\partial \vartheta (\mu , \nu) = L _ {\mu} \vartheta (\nu) - L _ {\nu} \vartheta (\mu)} \\ & {\qquad = - \frac {1 2}{\pi} \iint_ {\mathbb {D} ^ {*}} \iint_ {\mathbb {D} ^ {*}} \mu (w) \frac {g ^ {\prime} (w) ^ {2} g ^ {\prime} (z) ^ {2}}{(g (w) - g (z)) ^ {4}} \nu (z) d ^ {2} w d ^ {2} z} \\ & {\qquad + \frac {1 2}{\pi} \iint_ {\mathbb {D} ^ {*}} \iint_ {\mathbb {D} ^ {*}} \nu (w) \frac {g ^ {\prime} (w) ^ {2} g ^ {\prime} (z) ^ {2}}{(g (w) - g (z)) ^ {4}} \mu (z) d ^ {2} w d ^ {2} z} \\ & {\qquad = 0.} \end{array}
$$

4.2. Weil-Petersson potential on $T(1)$. The 1-form $\vartheta$ does not naturally extend to the whole Hilbert manifold $T(1)$ (since $\vartheta|_{[\mu]} \in A_2(\mathbb{D}^*)$ if and only if $[\mu] \in T_0(1)$). From Theorem 1.12 we also see that $T_0(1)$ is the maximal subset of $T(1)$ on which the function $S_1$ is well-defined. However, it is easy to construct a Weil-Petersson potential on $T(1)$ by using right translations. Namely, we index the components of the Hilbert manifold $T(1)$ by the set $I$ (uncountable) and for every $\alpha \in I$ choose $[\mu_\alpha] \in T_\alpha(1) = R_{\mu_\alpha}T_0(1)$ such that $\mu_0 = 0$ for the component $T_0(1)$. This represents $T(1)$ as a disjoint union

$$
T (1) = \bigsqcup_ {\alpha \in I} T _ {\alpha} (1).
$$

Define


> **[ERRATUM 4-4]** (5402–5406; Lean: `wpPotential`, S4_WPPotential) OCR error in the source text: `μ_{−1}^{−1}` should be `μ_α^{−1}`, and the doubled or unbalanced brackets `[[ … ]])` should be `([ν * μ_α^{−1}])`.

$$
\mathsf {S} ([ \nu ]) = \mathsf {S} _ {1} \left[ \left[ \nu * \mu_ {- 1} ^ {- 1} \right]\right) \quad \text {for} \quad [ \nu ] \in T _ {\alpha} (1).
$$

It follows from the right-invariance of the Weil-Petersson metric that the function $S$ is a Weil-Petersson potential on $T(1)$.

## 5. The period mapping

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026for download from IP 130.34.46.51.

The generalization of the classical period mapping to the homogeneous space  $\mathrm{Möb}(S^{1})\backslash\mathrm{Diff}_{+}(S^{1})$  was outlined by Kirillov and Yuriev in [KY88] and developed by Nag [Nag92]. In particular, in [Nag92] it is explained in what sense this is a generalization of classical period mapping as an association between the complex structures and corresponding spaces of holomorphic 1-forms. Subsequently in [NS95], Nag and Sullivan extended the period mapping to the universal Teichmüller space  $T(1)$ . Here we prove that the Kirillov-Yuriev-Nag-Sullivan (KYNS) period mapping coincides with the mapping  $\hat{P}$  defined in Remark 2.11.

<!-- page 107 of 136 -->

98

2. KÄHLER POTENTIAL AND PERIOD MAPPING

5.1. KYNS period mapping. Following [NS95], let $\mathcal{H}$ be the real Hilbert space

$$
\begin{array}{r l} & {\mathcal {H} = H ^ {1 / 2} (S ^ {1}, \mathbb {R}) / \mathbb {R}} \\ & {\quad = \left\{f: S ^ {1} \to \mathbb {R} \Big | f (e ^ {i \theta}) = \sum_ {n = - \infty} ^ {\infty^ {\prime}} c _ {n} e ^ {i n \theta}, \quad \sum_ {n = 1} ^ {\infty} n | c _ {n} | ^ {2} <   \infty \right\},} \end{array}
$$

and let $\Theta$ be the symplectic form$^2$ on $\mathcal{H}$:

$$
\Theta (f, g) = \frac {1}{2 \pi} \oint_ {S ^ {1}} g d f.
$$

By complex linearity, the symplectic form $\Theta$ extends to the complexification of $\mathcal{H}$ — the complex Hilbert space $\mathcal{H}_{\mathbb{C}}$,

$$
\left| \begin{array}{l} \mathcal {H} _ {\mathbb {C}} = H ^ {1 / 2} (S ^ {1}, \mathbb {C}) / \mathbb {C} \\ = \left\{f: S ^ {1} \to \mathbb {C} \Big | f (e ^ {i \theta}) = \sum_ {n = - \infty} ^ {\infty^ {\prime}} c _ {n} e ^ {i n \theta}, \quad \sum_ {n = - \infty} ^ {\infty^ {\prime}} | n | | c _ {n} | ^ {2} <   \infty \right\}. \end{array} \right.
$$

With respect to this symplectic form, the Hilbert space $\mathcal{H}_{\mathbb{C}}$ has a canonical decomposition into two closed isotropic subspaces

$$
\mathcal {H} _ {\mathbb {C}} = W _ {+} \oplus W _ {-},
$$

where

$$
W _ {+} = \left\{f: S ^ {1} \rightarrow \mathbb {C} \Big | f (e ^ {i \theta}) = \sum_ {n = 1} ^ {\infty} a _ {n} e ^ {i n \theta}, \quad \sum_ {n = 1} ^ {\infty} n | a _ {n} | ^ {2} <   \infty \right\},
$$

$$
W _ {-} = \left\{g: S ^ {1} \to \mathbb {C} \Big | g (e ^ {i \theta}) = \sum_ {n = 1} ^ {\infty} b _ {n} e ^ {- i n \theta}, \quad \sum_ {n = 1} ^ {\infty} n | b _ {n} | ^ {2} <   \infty \right\}.
$$

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026for download from IP 130.34.46.51.

Let $\mathfrak{D}_{\infty}$ be the infinite dimensional analog of Siegel disk [Sie64],

$$
\mathfrak {D} _ {\infty} = \Big \{Z \in \mathscr {B} (W _ {-}, W _ {+}): \Theta (Z f, g) = \Theta (Z g, f) \quad \text {and} \quad I - Z \bar {Z} > 0 \Big \}.
$$

Here $\mathcal{B}(W_{-}, W_{+})$ is the Banach space of all bounded linear operators from $W_{-}$ to $W_{+}$, and $\bar{Z} = JZJ : W_{+} \to W_{-}$, where $J$ is the standard conjugation operator on $\mathcal{H}_{\mathbb{C}}$ defined by $JW_{+} = W_{-}$. With respect to the standard bases

$$
\left\{e _ {n} = \frac {1}{\sqrt {n}} e ^ {i n \theta} \right\} _ {n \in \mathbb {N}} \quad \text {and} \quad \left\{f _ {n} = \frac {1}{\sqrt {n}} e ^ {- i n \theta} \right\} _ {n \in \mathbb {N}}
$$

of the subspaces $W_{+}$ and $W_{-}$, an operator $Z \in \mathfrak{D}_{\infty}$ is represented by an infinite matrix, and the condition $\Theta(Zf,g) = \Theta(Zg,f)$ translates as $Z = Z^t$. Let $\mathrm{Sp}(\mathcal{H})$ be the group of bounded symplectomorphisms on $\mathcal{H}$. Elements of $\mathrm{Sp}(\mathcal{H})$, extended complex linearly to $\mathcal{H}_{\mathbb{C}}$, in the basis $\{e_n\}_{n \in \mathbb{N}} \cup \{f_n\}_{n \in \mathbb{N}}$ of $\mathcal{H}_{\mathbb{C}}$ can be represented by matrices

$$
\left( \begin{array}{c c} A & B \\ \bar {B} & \bar {A} \end{array} \right), \quad \text {where} \quad A A ^ {*} - B B ^ {*} = I, A B ^ {t} = B A ^ {t}.\tag{5.1}
$$

The group $\mathrm{Sp}(\mathcal{H})$ acts transitively on $\mathfrak{D}_{\infty}$ by

$$
Z \mapsto (A Z + B) (\bar {B} Z + \bar {A}) ^ {- 1},
$$

<small><span class="docvortex-page-footnote" data-block-type="page_footnote" style="color:#6b7280">$^{2}$ We use a different sign convention since our complex structure has a different sign compared to [KY88, Nag92, NS95].</span></small>

<!-- page 108 of 136 -->

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

5. THE PERIOD MAPPING

99

and the stabilizer of the point $Z = 0$ is the unitary subgroup $U$ of $\mathrm{Sp}(\mathcal{H})$ consisting of bounded symplectomorphisms with $B = 0$. Thus the canonical quotient map $Q: \mathrm{Sp}(\mathcal{H}) \to \mathfrak{D}_{\infty}$,

$$
Q \left(\left( \begin{array}{c c} A & B \\ \bar {B} & \bar {A} \end{array} \right)\right) = (A Z + B) (\bar {B} Z + \bar {A}) ^ {- 1} \big | _ {Z = 0} = B \bar {A} ^ {- 1},
$$

induces the isomorphism

$$
\mathrm{Sp} (\mathcal {H}) / U \simeq \mathfrak {D} _ {\infty}.
$$

In [NS95], Nag and Sullivan proved that the assignment

$$
\mathrm{Homeo} _ {q s} (S ^ {1}) \ni \gamma \mapsto \hat {\Pi} (\gamma) \in \mathcal {B} (\mathcal {H} _ {\mathbb {C}}),
$$

where

$$
\hat {\Pi} (\gamma) (f) = f \circ \gamma - \frac {1}{2 \pi} \oint_ {S ^ {1}} f \circ \gamma d \theta , f \in \mathcal {H} _ {\mathbb {C}},
$$

defines a right action of the group $\mathrm{Homeo}_{qs}(S^1)$ on the Hilbert space $\mathcal{H}_{\mathbb{C}}$ by symplectomorphisms. Thus the mapping

$$
\hat {\Pi}: \operatorname{Homeo} _ {q s} (S ^ {1}) \to \operatorname{Sp} (\mathcal {H})
$$

satisfies $\hat{\Pi} (\gamma_1\circ \gamma_2) = \hat{\Pi} (\gamma_2)\hat{\Pi} (\gamma_1)$. On the other hand, an operator $\hat{\Pi} (\gamma)$ preserves the subspaces $W_{+}$ and $W_{-}$, i.e., $\hat{\Pi} (\gamma)\in U$, if and only if $\gamma \in \mathrm{Mob}(S^1)$. The induced mapping

$$
\Pi = Q \circ \hat {\Pi}: T (1) = \mathrm{Mob} (S ^ {1}) \backslash \mathrm{Homeo} _ {q s} (S ^ {1}) \to \mathrm{Sp} (\mathcal {H}) / U \simeq \mathfrak {D} _ {\infty}
$$

is what we call KYNS period mapping of $T(1)$.

With respect to the basis $\{e_n\}_{n\in \mathbb{N}}\cup \{f_n\}_{n\in \mathbb{N}}$ of $\mathcal{H}_{\mathbb{C}}$, the mapping

$$
\hat {\Pi}: \operatorname{Homeo} _ {q s} (S ^ {1}) \to \operatorname{Sp} (\mathcal {H})
$$

is given by the matrix

$$
\hat {\Pi} (\gamma) = \left( \begin{array}{c c} \mathfrak {A} & \mathfrak {B}, \\ \widetilde {\mathfrak {B}} & \widetilde {\mathfrak {A}} \end{array} \right), \quad \gamma \in \operatorname{Homeo} _ {q s} (S ^ {1}),
$$


> **[ERRATUM S5-01]** (TT:5539, 5567, 5571, 5614; Lean: `prop_5_1`, `matAB_spec`, `kyns` (Ch2/S5_PeriodMapping)) Notation/OCR slip: the inverse formula (TT:5560, `𝔄*`, `𝔅ᵗ`) and the proof (TT:5604–5606, "`B₁ = B₁ᵗ = 𝔅𝔄̄⁻¹`") require the entrywise conjugate; the tilde must be read as a bar.

where

$$
\mathfrak {A} _ {m n} (\gamma) = \frac {1}{2 \pi} \sqrt {\frac {m}{n}} \oint_ {S ^ {1}} \left(\gamma (e ^ {i \theta})\right) ^ {n} e ^ {- i m \theta} d \theta ,
$$

$$
\mathfrak {B} _ {m n} (\gamma) = \frac {1}{2 \pi} \sqrt {\frac {m}{n}} \oint_ {S ^ {1}} (\gamma (e ^ {i \theta})) ^ {- n} e ^ {- i m \theta} d \theta .
$$

As a result, the KYNS period matrix $\Pi : T(1) \to \mathfrak{D}_{\infty}$ is given by the matrix

$$
\Pi ([ \mu ]) = \mathfrak {B} \bar {\mathfrak {A}} ^ {- 1}, \quad [ \mu ] \in T (1),
$$

where $\mathfrak{A} = \mathfrak{A}(w_{\mu})$ and $\mathfrak{B} = \mathfrak{B}(w_{\mu})$. On the other hand, it follows from (5.1) that

$$
\hat {\Pi} (\gamma^ {- 1}) = \hat {\Pi} (\gamma) ^ {- 1} = \left( \begin{array}{c c} \mathfrak {A} (\gamma) ^ {*} & - \mathfrak {B} (\gamma) ^ {t} \\ - \mathfrak {B} (\gamma) ^ {*} & \mathfrak {A} (\gamma) ^ {t} \end{array} \right).
$$

PROPOSITION 5.1. The Grunsky matrices $B_{l}$, $l = 1,2,3,4$, corresponding to $\gamma \in S^{1} \backslash \text{Homeo}_{qs}(S^{1})$, and the elements of the matrix $\hat{\Pi}(\gamma)$ are related by

$$
B _ {1} = \mathfrak {B} \widetilde {\mathfrak {A}} ^ {- 1}, \quad B _ {2} = (\mathfrak {A} ^ {*}) ^ {- 1},
$$

$$
B _ {3} = \widetilde {\mathfrak {A}} ^ {- 1}, \qquad B _ {4} = - \mathfrak {B} ^ {*} (\mathfrak {A} ^ {*}) ^ {- 1}.
$$

<!-- page 109 of 136 -->

100

2. KÄHLER POTENTIAL AND PERIOD MAPPING

PROOF. Let $\gamma = g^{-1} \circ f$ be the conformal welding of $\gamma \in S^{1} \backslash \mathrm{Homeo}_{qs}(S^{1})$, and let $P_{n}$ and $Q_{n}$ be the Faber polynomials associated to the pair $(f, g)$. Denoting by $\mathrm{P}_{+}: \mathcal{H}_{\mathbb{C}} \to W_{+}$ and $\mathrm{P}_{-}: \mathcal{H}_{\mathbb{C}} \to W_{-}$ the orthogonal projection operators, we get

$$
\mathfrak {A} ^ {*} = \mathrm{P} _ {+} \hat {\Pi} (\gamma^ {- 1}) \Big | _ {W _ {+}}.
$$

By definition of Faber polynomials, $(P_n^0\circ f)\big|_{S^1}\in W_+$, where $P_{n}^{0}(z) = P_{n}(z) - P_{n}(0)$ and $n\geq 1$. We have on $S^1$,

$$
\mathrm{P} _ {+} \hat {\Pi} (\gamma^ {- 1}) (P _ {n} ^ {0} \circ f) = \mathrm{P} _ {+} \left((P _ {n} ^ {0} \circ f) \circ f ^ {- 1} \circ g\right) = \mathrm{P} _ {+} (P _ {n} ^ {0} \circ g).
$$

Since $\mathrm{P}_{+}(P_{n}^{0}\circ g)(e^{i\theta}) = e^{in\theta}$ and $(P_n^0\circ f)(e^{i\theta}) = n\sum_{m = 1}^{\infty}b_{-m,n}e^{im\theta}$, we obtain

$$
\sum_ {k = 1} ^ {\infty} \mathfrak {A} _ {m k} ^ {*} (B _ {2}) _ {k n} = \delta_ {m n},
$$

i.e. $\mathfrak{A}^* B_2 = \mathrm{Id}$. Similarly, let $Q_{n}^{0} = Q_{n} - Q_{n}(\infty)$. By definition of Faber polynomials, $(Q_{n}^{0}\circ f)(e^{i\theta}) - e^{-in\theta}\in W_{+}$ for $n\geq 1$. We have on $S^1$,

$$
\mathrm{P} _ {+} \hat {\Pi} (\gamma^ {- 1}) ((Q _ {n} ^ {0} (f (e ^ {i \theta})) - e ^ {- i n \theta}) = \mathrm{P} _ {+} \left((Q _ {n} ^ {0} \circ g) - (\gamma^ {- 1}) ^ {- n}\right) = - \mathrm{P} _ {+} ((\gamma^ {- 1}) ^ {- n}).
$$

Since $-\mathfrak{B}(\gamma^{-1}) = \mathfrak{B}^t$, we have $-\mathrm{P}_{+}((\gamma^{-1})^{-n})(e^{i\theta}) = \sum_{k=1}^{\infty} \sqrt{\frac{n}{k}} \mathfrak{B}_{nk} e^{ik\theta}$. Using $Q_n^0(f(e^{i\theta})) - e^{-in\theta} = n \sum_{m=1}^{\infty} b_{-m,-n} e^{im\theta}$, we obtain

$$
\left| \sum_ {k = 1} ^ {\infty} \mathfrak {A} _ {m k} ^ {*} (B _ {1}) _ {k n} = \mathfrak {B} _ {n m}, \right.
$$

i.e., $\mathfrak{A}^* B_1 = \mathfrak{B}^t$, which is equivalent to $B_{1} = B_{1}^{t} = \mathfrak{B}\bar{\mathfrak{A}}^{-1}$. Using $B_{3} = B_{2}^{t}$ and $B_{4}(\gamma) = \overline{B_{1}(\gamma^{-1})}$ concludes the proof.

COROLLARY 5.2. The KYNS period mapping $\Pi$ coincides with our period mapping $\hat{\mathcal{P}}$ defined in Remark 2.11.

PROOF. Due to Proposition 5.1, $B_{1} = \mathfrak{B}\tilde{\mathfrak{A}}^{-1}$.

REMARK 5.3. In [NS95] it was stated that the period mapping $\Pi : T(1) \to \mathfrak{D}_{\infty}$ is a holomorphic mapping of Banach manifolds. However, it was only shown that the induced mapping $D\Pi$ of tangent spaces is complex linear injection, which is not enough to claim holomorphy for infinite dimensional manifolds. In Appendix B we prove that the mapping $\hat{\mathcal{P}} : T(1) \to \mathcal{B}(\ell^2)$ is holomorphic, which completes the proof in [NS95].

Following G. Segal [Seg81], we introduce the subgroup $\mathrm{Sp}_0(\mathcal{H})$ of the symplectic group $\mathrm{Sp}(\mathcal{H})$ for which $B\in \mathcal{S}_2(W_-,W_+)$ — the Hilbert space of Hilbert-Schmidt operators from $W_{-}$ to $W_{+}$. The group $\mathrm{Sp}_0(\mathcal{H})$ acts transitively on the restricted Siegel disc

$$
\mathfrak {D} _ {\infty} ^ {0} = \mathfrak {D} _ {\infty} \cap \mathscr {S} _ {2} (W _ {-}, W _ {+}).
$$

Corollaries 5.2 and 2.9 immediately imply the following result.

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026for download from IP 130.34.46.51.

COROLLARY 5.4. For $[\mu] \in T(1)$, $\Pi([\mu]) \in \mathfrak{D}_{\infty}^{0}$ if and only if $[\mu] \in T_{0}(1)$.

<!-- page 110 of 136 -->

5. THE PERIOD MAPPING

101

REMARK 5.5. In view of the above corollary, define the restricted period mapping

$$
\Pi_ {0} = \Pi | _ {T _ {0} (1)}: T _ {0} (1) \to \mathfrak {D} _ {\infty} ^ {0}.
$$

Since by Corollary 5.2 $\Pi_0 = \mathcal{P}$, by Theorem 2.10 $\Pi_0$ is a holomorphic mapping of Hilbert manifolds. The homogenous space $\mathfrak{D}_{\infty}^{0}$ carries a natural $\mathrm{Sp}_0(\mathcal{H})$-invariant Kähler metric with the Kähler potential $\Phi(Z) = \log \mathrm{Det}(1 - Z\bar{Z})$. It was first shown by Kirillov and Yuriev [KY88] and later by Nag [Nag92] that the pullback of this metric to $\mathrm{Möb}(S^1)\backslash \mathrm{Diff}_+(S^1)$ by the period mapping coincides, up to a constant, with the Weil-Petersson metric. It immediately follows from Corollary 5.2 that

$$
S _ {2} = \log \operatorname{Det} (I - Z \bar {Z}),
$$

so that the pullback of the natural Kähler metric on  $D_{\infty}^{0}$  by the restricted period mapping to  $T_{0}(1)$  coincides, up to a constant, with the Weil-Petersson metric on  $T_{0}(1)$ . Thus we have established the relations between all natural potential functions on  $T_{0}(1)$ : up to a constant factor, they are indeed all equal!

5.2. Embeddings into the Segal-Wilson universal Grassmannian. Let $\mathcal{V}$ be an infinite-dimensional separable complex Hilbert space and let

$$
\mathcal {V} = V _ {+} \oplus V_{-}
$$

be its decomposition into the direct sum of infinite-dimensional closed subspaces $V_{+}$ and $V_{-}$. The Segal-Wilson universal Grassmannian $\mathrm{Gr}(\mathcal{V})$ [SW85, PS86] is defined as a set of closed subspaces $W$ of $\mathcal{V}$ satisfying the following conditions.

UG1. The orthogonal projection $\mathrm{pr}_{+}:W\to V_{+}$ is a Fredholm operator.

UG2. The orthogonal projection $\mathrm{pr}_{-}:W\to V_{-}$ is a Hilbert-Schmidt operator. Equivalently, $W\in \mathrm{Gr}(\mathcal{V})$, if $W$ is the image of an operator $\mathrm{w}:V_{+}\to W$ such that $\mathrm{pr}_{+}\mathrm{w}$ is Fredholm and $\mathrm{pr}_{-}\mathrm{w}$ is Hilbert-Schmidt. The Segal-Wilson Grassmannian $\mathrm{Gr}(\mathcal{V})$ is a Hilbert manifold modeled on the Hilbert space $\mathcal{S}_2(V_+,V_-)$ of Hilbert-Schmidt operators from $V_{+}$ to $V_{-}$.

For our purposes, let $\mathcal{V} = \mathcal{H}_{\mathbb{C}}$ and $V_{+} = W_{-}$, $V_{-} = W_{+}$. To every $[\mu] \in T_0(1)$ we associate a closed subspace $W_{\mu} \subset \mathcal{H}_{\mathbb{C}}$ spanned by the functions $w_n(e^{i\theta}) = \frac{1}{\sqrt{n}} Q_n(\mathrm{f}^{\mu}(e^{i\theta}))$, where $w_{\mu} = \mathrm{g}_{\mu}^{-1} \circ \mathrm{f}^{\mu}$ is the corresponding conformal welding. Explicitly, in terms of the basis $\{e_n\}_{n \in \mathbb{N}} \cup \{f_n\}_{n \in \mathbb{N}}$ of $\mathcal{H}_{\mathbb{C}}$,

$$
\left| w _ {n} = f _ {n} + \sum_ {m = 1} ^ {\infty} \sqrt {n m} b _ {- n, - m} e _ {m}, n \in \mathbb {N}. \right.
$$

We have $W_{\mu} = \mathrm{w}(V_{+})$, where $\mathrm{w}(f_n) = w_n$, $n \in \mathbb{N}$. Thus the mapping $\mathrm{pr}_{+}\mathrm{w} = I$ — the identity operator on $V_{+}$, is obviously Fredholm, and the mapping $\mathrm{pr}_{-}\mathrm{w} = B_1(\mathrm{f}^{\mu})$ is Hilbert-Schmidt since $[\mu] \in T_0(1)$. According to Theorem 2.10, the mapping

$$
\mathcal {E}: T _ {0} (1) \to \mathrm{Gr} (\mathcal {H} _ {\mathbb {C}})
$$

given by $\mathcal{E}([\mu]) = W_{\mu}$ is a holomorphic inclusion of $T_0(1)$ into the Segal-Wilson universal Grassmannian. For the homogeneous space $\mathrm{Möb}(S^1)\backslash \mathrm{Diff}_+(S^1)$ this mapping was first considered in [KY88].

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026for download from IP 130.34.46.51.

REMARK 5.6. Seemingly another mapping of $\mathrm{Möb}(S^1) \backslash \mathrm{Diff}_+(S^1)$ into the Segal-Wilson Grassmannian was considered in [STZ99]. Namely, extend $\mu \in L^\infty(\mathbb{D}^*)$ by zero to $\mathbb{D}$ and let $V_\mu$ be the space of distributional solutions of the Beltrami equation $w_{\bar{z}} = \mu w_z$ on $\mathbb{C}$ having a single pole at 0. The mapping in [STZ99]

<!-- page 111 of 136 -->

102

2. KÄHLER POTENTIAL AND PERIOD MAPPING

was defined by the assignment $[\mu] \to V_{\mu}|_{S^{1}}$. It is easy to see that the space $V_{\mu}$ is spanned by the functions $w_{n}(z) = Q_{n}(\mathrm{f}^{\mu})(z)$, $n \in \mathbb{N}$, so that $V_{\mu}|_{S^{1}} = W_{\mu}$ and the mapping in [STZ99] coincides with the Kirillov-Yuriev mapping [KY88].

REMARK 5.7. The inclusion $\mathcal{E}: T_0(1) \to \mathrm{Gr}(\mathcal{H}_{\mathbb{C}})$ is a holomorphic mapping due to the holomorphic dependence of $f^\mu$ on $\mu$. Since $f^\mu$ is holomorphic on $\mathbb{D}$, the subspaces $W_\mu$ correspond to the different uniformizations of the same Riemann surface $\Omega = f^\mu(\mathbb{D}) \simeq \mathbb{D}$. However, one can consider another mapping where the associated subspaces in the universal Grassmannian correspond to Riemann surfaces of different complex structure. Namely, set, as before, $\mathcal{V} = \mathcal{H}_{\mathbb{C}}$ and let $V_+ = W_+$ and $V_- = W_-$. We denote the corresponding Segal-Wilson Grassmannian by $\widetilde{\mathrm{Gr}}(\mathcal{H}_{\mathbb{C}})$, and define the mapping

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026for download from IP 130.34.46.51.

$$
\widetilde {\mathcal {E}}: T _ {0} (1) \to \widetilde {\mathrm{Gr}} (\mathcal {H} _ {\mathbb {C}})
$$

by assigning to every point $[\mu] \in T_0(1)$ the closed subspace $\tilde{W}_{\mu} \subset \mathcal{H}_{\mathbb{C}}$ spanned by the functions $\tilde{w}_n(e^{i\theta}) = \frac{1}{\sqrt{n}} P_n(\mathrm{g}_{\mu}(e^{i\theta}))$, $n \in \mathbb{N}$. We have $\tilde{W}_{\mu} = \tilde{\mathrm{w}}(V_{+})$, where $\tilde{\mathrm{w}}(e_n) = \tilde{w}_n$, $n \in \mathbb{N}$, and $\mathrm{pr}_{+}\tilde{\mathrm{w}} = I$ — the identity operator on $V_{+}$ and $\mathrm{pr}_{-}\tilde{\mathrm{w}} = B_4(\mathrm{g}_{\mu})$ is Hilbert-Schmidt since $[\mu] \in T_0(1)$. The mapping $\tilde{\mathcal{E}}$ is not holomorphic. However, since $JW_{+} = W_{-}$, where $J$ is the standard conjugation operator on $\mathcal{H}_{\mathbb{C}}$, we have $\widetilde{\mathrm{Gr}}(\mathcal{H}_{\mathbb{C}}) = J(\mathrm{Gr}(\mathcal{H}_{\mathbb{C}}))$, so that $\widetilde{\mathrm{Gr}}(\mathcal{H}_{\mathbb{C}})$ is a mirror image of $\mathrm{Gr}(\mathcal{H}_{\mathbb{C}})$. Denoting by $\mathcal{I}$ the inversion on the topological group $T_0(1)$, we get

$$
\tilde {\mathcal {E}} = J \circ \mathcal {E} \circ \mathcal {I}.
$$

REMARK 5.8. One can describe the “Schottky locus”, i.e., the image $\mathcal{E}(T_0(1))$ in the Segal-Wilson Grassmannian $\mathrm{Gr}(\mathcal{H}_{\mathbb{C}})$. Indeed, since the corresponding points in $\mathrm{Gr}(\mathcal{H}_{\mathbb{C}})$ are associated with the Grunsky operators $B_1$, it is equivalent to the characterization of the image of the restricted period map $\Pi_0: T_0(1) \to \mathfrak{D}_\infty^0$. Let $C = \{C_{mn}\}_{m,n \in \mathbb{N}} \in \mathfrak{D}_\infty^0$, which we realized as symmetric, Hilbert-Schmidt operator on $\ell^2$ satisfying $I - C\tilde{C} > 0$. Then $C \in \Pi_0(T_0(1))$ if and only if the following conditions are satisfied.

S1.

$$
1 + \sum_ {m = 1} ^ {\infty} \frac {C _ {m 1}}{\sqrt {m}} \frac {z _ {1} ^ {m} - z _ {2} ^ {m}}{z _ {1} ^ {- 1} - z _ {2} ^ {- 1}} = \exp \left(- \sum_ {m, n = 1} ^ {\infty} \frac {C _ {m n}}{\sqrt {m n}} z _ {1} ^ {m} z _ {2} ^ {n}\right).
$$

S2. There exist $D = \{D_{mn}\}_{m,n\in \mathbb{N}}\in \mathfrak{D}_{\infty}^{0}$ and $B\in \mathcal{B}(\ell^2)$ such that

$$
I - C \bar {C} = B B ^ {*} \quad \text {and} \quad I - D \bar {D} = \bar {B} ^ {*} \bar {B}.
$$

S3.

$$
1 + \sum_ {m = 1} ^ {\infty} \frac {D _ {m 1}}{\sqrt {m}} \frac {z _ {1} ^ {- m} - z _ {2} ^ {- m}}{z _ {1} - z _ {2}} = \exp \left(- \sum_ {m, n = 1} ^ {\infty} \frac {D _ {m n}}{\sqrt {m n}} z _ {1} ^ {- m} z _ {2} ^ {- n}\right).
$$

Equations S1 and S3 are understood as infinite sequence of relations between elements of the matrices $C$ and $D$ obtained by comparing coefficients of $z_1^m z_2^n$ and $z_1^{-m}z_2^{-n}$ respectively. Equations S1 and S3 are nothing but dispersionless Hirota equations (see, e.g., [Teo03]). They are just a reformulation of the definition of

<!-- page 112 of 136 -->

5. THE PERIOD MAPPING

103

the Grunsky coefficients of the univalent functions $f$ and $g$ and the identities

$$
\frac {1}{f (z)} + c = Q _ {1} (f (z)) = \frac {1}{z} + \sum_ {m = 1} ^ {\infty} b _ {- 1, - m} z ^ {m},
$$

$$
\frac {g (z)}{b} + d = P _ {1} (g (z)) = z + \sum_ {m = 1} ^ {\infty} b _ {1 m} z ^ {- m},
$$

where $c$ and $d$ are constants. See [Teo03] for details.

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

<!-- page 113 of 136 -->

This page intentionally left blank

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

<!-- page 114 of 136 -->

## APPENDIX A

## The Hilbert Manifold Structure of $\mathcal{T}_0(1)$

Here we show that the Hilbert manifold $\mathcal{T}_0(1)$, modeled on the Hilbert space $A_2(\mathbb{D})\oplus \mathbb{C}$, can also be modeled on the Hilbert space $A_2^1 (\mathbb{D})$, which induce the same Hilbert manifold structure. This result is parallel to the one in the Appendix of [Teo04].

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026for download from IP 130.34.46.51.

Let $\beta$ be the Bers embedding $\mathcal{T}(1)\hookrightarrow A_{\infty}(\mathbb{D})\oplus \mathbb{C}$,

$$
\mathcal {T} (1) \ni \gamma = g ^ {- 1} \circ f \mapsto \left(\mathcal {S} (f), \frac {1}{2} \mathcal {A} (f) (0)\right),
$$

and let $\hat{\beta}:\mathcal{T}(1)\to A_{\infty}^{1}(\mathbb{D})$ be the pre-Bers embedding of $\mathcal{T}(1)$ into $A_{\infty}^{1}(\mathbb{D})$,

$$
\mathcal {T} (1) \ni \gamma = g ^ {- 1} \circ f \mapsto \mathcal {A} (f).
$$

By Theorem 1.12, $\hat{\beta} (\gamma)\in A_2^1 (\mathbb{D})$ if and only if $\gamma \in \mathcal{T}_0(1)$.

LEMMA A.1. The map $\widehat{\Psi}:A_2^1 (\mathbb{D})\to A_2(\mathbb{D})\oplus \mathbb{C}$

$$
\widehat {\Psi} (\psi) = \left(\Psi (\psi), \frac {1}{2} \psi (0)\right),
$$

where $\Psi (\psi) = \psi_{z} - \frac{1}{2}\psi^{2}$, is a one to one holomorphic mapping on Hilbert spaces.

PROOF. Firstly, the map $\Psi : A_2^1(\mathbb{D}) \to A_2(\mathbb{D})$ is holomorphic. That is, for every $\psi, \varphi \in A_2^1(\mathbb{D})$, the map $\mathbb{C} \ni t \mapsto \Psi(\psi + t\varphi)$ is holomorphic in a neighbourhood of $0 \in \mathbb{C}$. Indeed,

$$
\left\| \frac {\Psi (\psi + t \varphi) - \Psi (\psi + t _ {0} \varphi)}{t - t _ {0}} - \frac {d}{d t} \Big | _ {t = t _ {0}} \Psi (\psi + t \varphi) \right\| _ {A _ {2} (\mathbb {D})}
$$

$$
= \frac {\left| t - t _ {0} \right|}{2} \| \varphi^ {2} \| _ {A _ {2} (\mathbb {D})} \leq \frac {\left| t - t _ {0} \right|}{4} \| \varphi \| _ {A _ {\infty} ^ {1} (\mathbb {D})} \| \varphi \| _ {A _ {2} ^ {1} (\mathbb {D})} = O (| t - t _ {0} |).
$$

Secondly, by Lemma 1.3,

$$
| \psi (0) | \leq \sqrt {\frac {1}{\pi}} \| \psi \| _ {A _ {2} ^ {1} (\mathbb {D})},
$$

so that $\psi \mapsto \frac{1}{2}\psi (0)$ is a bounded complex-linear map. The injectivity of $\widehat{\Psi}$ has been proved in the Appendix of [Teo04].

COROLLARY A.2. The set $\hat{\beta} (\mathcal{T}_0(1))\subset A_2^1 (\mathbb{D})$ is open in $A_2^1 (\mathbb{D})$

PROOF. It readily follows from the results in Section 3.3 of Part I that $\beta(\mathcal{T}_0(1))$ is open in $A_2(\mathbb{D}) \oplus \mathbb{C}$. The assertion now follows from the lemma above since $\hat{\beta}(\mathcal{T}_0(1)) = \widehat{\Psi}^{-1}\big(\beta(\mathcal{T}_0(1))\big)$.

THEOREM A.3. The embeddings $\beta : \mathcal{T}_0(1) \hookrightarrow A_2(\mathbb{D}) \oplus \mathbb{C}$ and $\hat{\beta}: \mathcal{T}_0(1) \hookrightarrow A_2^1(\mathbb{D})$ induce the same Hilbert manifold structure on $\mathcal{T}_0(1)$.

105

<!-- page 115 of 136 -->

106

A. THE HILBERT MANIFOLD STRUCTURE OF $\mathcal{T}_0(1)$

PROOF. The map $\widehat{\Psi}:\hat{\beta}(\mathcal{T}_{0}(1))\to\beta(\mathcal{T}_{0}(1))$ is a holomorphic bijection between complex manifolds. To show that $\widehat{\Psi}$ is biholomorphic, by inverse function theorem (see, e.g., [Lan95]) we need to prove that for every $\psi\in\hat{\beta}(\mathcal{T}_{0}(1))$ the linear map $D_{\psi}\widehat{\Psi}$ is a topological isomorphism between the Hilbert spaces $A_{2}^{1}(\mathbb{D})$ and $A_{2}(\mathbb{D})\oplus\mathbb{C}$. Let $\gamma=g^{-1}\circ f\in\mathcal{T}_{0}(1)$ and $\psi=\mathcal{A}(f)\in\hat{\beta}(\mathcal{T}_{0}(1))$. The linear map $D_{\psi}\widehat{\Psi}:A_{2}^{1}(\mathbb{D})\to A_{2}(\mathbb{D})\oplus\mathbb{C}$ is given by

$$
\varphi \mapsto \left(\varphi_ {z} - \psi \varphi , \frac {1}{2} \varphi (0)\right).
$$

For every $(\phi, c) \in A_2(\mathbb{D}) \oplus \mathbb{C}$, the holomorphic function $\varphi$ on $\mathbb{D}$, defined by

$$
\varphi (z) = f ^ {\prime} (z) \left(\int_ {0} ^ {z} \frac {\phi (u)}{f ^ {\prime} (u)} d u + 2 c\right),
$$

satisfies

$$
\varphi_ {z} - \psi \varphi = \phi \quad \text {and} \quad \frac {1}{2} \varphi (0) = c.
$$

We claim that $\varphi \in A_2^1 (\mathbb{D})$, so that the map $D_{\psi}\hat{\Psi}$ is onto. Indeed, repeating the proof of Lemma 1.11, we get for $z\in \mathbb{D}$,

$$
| \phi (z) | ^ {2} \geq \frac {1}{2} | \varphi_ {z} | ^ {2} - | \psi (z) | ^ {2} | \varphi (z) | ^ {2}.
$$

By Becker-Pommerenke theorem, there exists $r' > 0$ such that

$$
| (1 - | z | ^ {2}) \psi (z) | \leq \frac {1}{2 \sqrt {2}} \quad \text {for all} \quad r ^ {\prime} <   | z | <   1.
$$

Thus for $r' < |z| < 1$,

$$
2 (1 - | z | ^ {2}) ^ {2} | \phi (z) | ^ {2} \geq (1 - | z | ^ {2}) ^ {2} | \varphi_ {z} (z) | ^ {2} - \frac {1}{4} | \varphi (z) | ^ {2},
$$

and the result follows as in the proof of Lemma 1.11. Uniqueness theorem for differential equations guarantees that the map $D_{\psi} \hat{\Psi}$ is one-to-one. Finally, by using the same arguments as in the proof of Lemma 1.5 and Lemma 1.3, there exists $C > 0$ such that for all $\varphi \in A_2^1(\mathbb{D})$,

$$
\| D _ {\psi} \hat {\Psi} (\varphi) \| _ {A _ {2} (\mathbb {D})} \leq C \| \varphi \| _ {A _ {2} ^ {1} (\mathbb {D})}.
$$

Hence $D_{\psi}\hat{\Psi}$ is a bounded linear bijection between Hilbert spaces.

COROLLARY A.4. Let $\{\gamma_n\}_{n=1}^{\infty}$ be a sequence of points in $\mathcal{T}_0(1)$, $\gamma_n = g_n^{-1} \circ f_n$, and let $\gamma = g^{-1} \circ f \in \mathcal{T}_0(1)$. Then the following conditions are equivalent.


> **[IMPLICIT HYPOTHESIS A-6]** (5858, 5928; Lean: topology of `𝒯₀(1)`, A_HilbertStructure (cor_A_4, cor_A_6)) The memoir uses this topology implicitly.

(i) In $\mathcal{T}_0(1)$ topology,

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

$$
\lim _ {n \to \infty} \gamma_ {n} = \gamma .
$$

(ii) In $A_2^1 (\mathbb{D})$ topology,

$$
\lim _ {n \to \infty} \mathcal {A} (f _ {n}) (z) = \mathcal {A} (f) (z).
$$

(iii) In $A_2^1 (\mathbb{D}^*)$ topology,

$$
\lim _ {n \to \infty} \left(\mathcal {A} (g _ {n}) (z) - 2 \frac {g _ {n} ^ {\prime} (z)}{g _ {n} (z)} + \frac {2}{z}\right) = \mathcal {A} (g) (z) - 2 \frac {g ^ {\prime} (z)}{g (z)} + \frac {2}{z}.
$$

<!-- page 116 of 136 -->

A. THE HILBERT MANIFOLD STRUCTURE OF $\mathcal{T}_0(1)$

107

PROOF. The equivalence (i)⇔(ii) follows from Theorem A.3. Since  $\mathcal{T}_{0}(1)$  is a topological group,  $\lim_{n\to\infty}\gamma_{n}=\gamma$  if and only if  $\lim_{n\to\infty}\gamma_{n}^{-1}=\gamma^{-1}$ . Now let  $j(z)=\frac{1}{z}$  and let r be the dilation  $z\mapsto\overline{g'(\infty)}z$ . We have  $\gamma^{-1}=\tilde{g}^{-1}\circ\tilde{f}$ , where  $\tilde{f}=r\circ j\circ g\circ j$  and

$$
\mathcal {A} (\tilde {f}) = \mathcal {A} (r \circ j \circ g \circ j) = \left(\mathcal {A} (g) - 2 \frac {g ^ {\prime}}{g} + 2 \bar {j}\right) \circ j j _ {\bar {z}},
$$

so that the equivalence (i)⇔(iii) follows from the equivalence (i)⇔(ii). □

Next, consider the mappings $\beta^{*}:T_{0}(1)\to A_{2}(\mathbb{D}^{*})$,

$$
\beta^ {\star} (\gamma) = \overline {{\beta (\gamma^ {- 1}) \circ j j _ {z} ^ {2}}} = \mathcal {S} (g),
$$

and $\hat{\beta}^{*}:\mathcal{T}_{0}(1)\to A_{2}^{1}(\mathbb{D}^{*})$,

$$
\hat {\beta} ^ {*} (\gamma) = \mathcal {A} (g),
$$

where $\gamma = g^{-1} \circ f \in \mathcal{T}_0(1)$. Also, consider the mapping $\Psi^*: A_2^1(\mathbb{D}^*) \to A_2(\mathbb{D}^*)$, defined by

$$
\Psi^ {*} (\psi) = \psi_ {z} - \frac {1}{2} \psi^ {2},
$$

and let

$$
\widetilde {A _ {2} ^ {1}} (\mathbb {D} ^ {*}) = \left\{\psi \in A _ {2} ^ {1} (\mathbb {D} ^ {*}): \psi (z) = O \left(\frac {1}{z ^ {3}}\right) \text {as} z \to \infty \right\}.
$$

We have the following result.

LEMMA A.5.


> **[ERRATUM A-1]** (5920–5922; Lean: `lemma_A_5` (i), AppACompleted2) False: for ψ = z⁻² ∈ A₂¹(𝔻*), Ψ*(ψ) = ψ' − ½ψ² ∼ −2z⁻³ ∉ A₂(𝔻*) (log-divergent at ∞; cf. Lemma 1.5). Correct version: Ψ* maps `Ã₂¹(𝔻*)` into `A₂(𝔻*)` (and is injective there).

(i) The map $\Psi^{*}: A_{2}^{1}(\mathbb{D}^{*}) \to A_{2}(\mathbb{D}^{*})$ is a holomorphic mapping on Hilbert spaces and its restriction to the subspace $\widetilde{A_{2}^{1}}(\mathbb{D}^{*})$ is injective.

(ii) The set $\hat{\beta}^{*}(\mathcal{T}_{0}(1)) = \hat{\beta}^{*}(T_{0}(1))$ is open in $A_2^1 (\mathbb{D}^*)$.


> **[ERRATUM A-2]** (5924; Lean: `lemma_A_5` (ii), AppACompleted2) False as stated: `Ã₂¹(𝔻*)` is a proper closed subspace of `A₂¹(𝔻*)` and contains β̂*(𝒯₀(1)) (𝒜(g) = O(z⁻³) for g univalent at ∞), so no nonempty subset of it is open in `A₂¹(𝔻*)`. Correct version: open in `Ã₂¹(𝔻*)`.

PROOF. Holomorphy of $\Psi^{*}$ is proved along the same lines as Lemma A.1. From the proof of Theorem A.5 in [Teo04] it follows that the restriction of the map $\Psi^{*}$ to the subspace $\widetilde{A_{2}^{1}}(\mathbb{D}^{*})$ is one to one. To prove part (ii), observe that $\beta^{*} = \Psi^{*} \circ \hat{\beta}^{*}$ and $\beta^{*}(\mathcal{T}_{0}(1)) = \beta^{*}(T_{0}(1))$. Since $\hat{\beta}^{*}(\mathcal{T}_{0}(1)), \hat{\beta}^{*}(T_{0}(1)) \in \widetilde{A_{2}^{1}}(\mathbb{D}^{*})$ and the restriction of $\Psi^{*}$ to $\widetilde{A_{2}^{1}}(\mathbb{D}^{*})$ is injective, we have the equality $\hat{\beta}^{*}(\mathcal{T}_{0}(1)) = \hat{\beta}^{*}(T_{0}(1))$. The proof that this set is open in $A_{2}^{1}(\mathbb{D}^{*})$ is analogous to the proof of Corollary A.2.

COROLLARY A.6. Let $\{\gamma_n\}_{n=1}^{\infty}$, $\gamma_n = g_n^{-1} \circ f_n$, be a sequence of points in $\mathcal{T}_0(1)$ such that


> **[ERRATUM A-3]** (5928–5948; Lean: `cor_A_6`, A_HilbertStructure) OCR rendering of `lim` in the source text; clause (ii) of the same corollary has `lim`.

$$
\varliminf_ {n \to \infty} \gamma_ {n} = \gamma = g ^ {- 1} \circ f \in \mathcal {T} _ {0} (1).
$$

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

Then the following statements hold.

(i) In $A_{2}(\mathbb{D}^{*})$ topology,

$$
\varliminf_ {n \to \infty} \mathcal {S} (g _ {n}) = \mathcal {S} (g).
$$

(ii) In $A_2^1 (\mathbb{D}^*)$ topology,

$$
\lim _ {n \to \infty} \mathcal {A} (g _ {n}) = \mathcal {A} (g).
$$

<!-- page 117 of 136 -->

108

A. THE HILBERT MANIFOLD STRUCTURE OF $\mathcal{T}_0(1)$

PROOF. Since $\mathcal{T}_0(1)$ is a topological group, $\lim_{n\to \infty}\gamma_n^{-1} = \gamma^{-1} = \tilde{g}^{-1}\circ \tilde{f}$. We have $\tilde{f} = r\circ j\circ g\circ j$, so that

$$
\mathcal {S} (\hat {f}) = \overline {{\mathcal {S} (g) \circ j j _ {\xi} ^ {2}}},
$$

which proves part (i). Part (ii) follows from Lemma A.5.

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

<!-- page 118 of 136 -->

## APPENDIX B

## The Period Mapping $\hat{\mathcal{P}}$

Let $\mathcal{S}_{\infty}$ be the closed ideal of compact operators in the Banach algebra $\mathcal{B}(\ell^2)$ of bounded operators on $\ell^2$. Here we prove that the period mapping $\hat{\mathcal{P}}: T(1) \to \mathcal{B}(\ell^2)$, defined in Remark 2.11, is a holomorphic mapping of complex Banach manifolds and that

$$
\hat {\mathcal {P}} ^ {- 1} (\mathcal {S} _ {\infty}) = S = \mathrm{M} \mathrm{ob} (S ^ {1}) \backslash \mathrm{Homeo} _ {s} (S ^ {1}).
$$

THEOREM B.1. The inclusion $\hat{\mathcal{P}}: T(1) \to \mathcal{B}(\ell^2)$ is a holomorphic mapping of Banach manifolds.

PROOF. As in the proof of Theorem 2.10, we will show that for every $[\nu] \in T(1)$ and $\mu \in \Omega^{-1,1}(\mathbb{D}^*)$, the map $\mathbb{C} \ni t \mapsto B_1(t) = B_1(f^{\nu + t\mu})$ is holomorphic in a neighborhood of $t = 0$ in $\mathbb{C}$. Choose $\delta > 0$ so that $\| \nu + t\mu \|_{\infty} < 1$ for all $|t| < \delta$. For every $t_0$ such that $|t_0| < \delta$, let $\delta_1$ be such that $0 < \delta_1 < \delta - |t_0|$. Then for all $|t - t_0| < \delta_1$, we have as in Theorem 2.10,

$$
\begin{array}{c} \left(K _ {1} ^ {\nu + t \mu} - K _ {1} ^ {\nu + t _ {0} \mu} - (t - t _ {0}) \left. \frac {d}{d t} \right| _ {t = t _ {0}} K _ {1} ^ {\nu + t \mu}\right) (z, w) \\ = \frac {(t - t _ {0}) ^ {2}}{2 \pi i} \oint_ {| \zeta - t _ {0} | = \delta_ {1}} \frac {K _ {1} ^ {\nu + \zeta \mu} (z , w)}{(\zeta - t) (\zeta - t _ {0}) ^ {2}} d \zeta . \end{array}
$$

This gives

$$
\begin{array}{c}\left\| \frac {B _ {1} (\mathrm{f} ^ {\nu + t \mu}) - B _ {1} (\mathrm{f} ^ {\nu + t _ {0} \mu})}{t - t _ {0}} - \frac {d}{d t} \bigg | _ {t = t _ {0}} B _ {1} (\mathrm{f} ^ {\nu + t \mu}) \right\|\\= \sup _ {\| u \| _ {2} = 1} \left(\iint_ {\mathbb {D}} \left| \iint_ {\mathbb {D}} \frac {t - t _ {0}}{2 \pi i} \oint_ {| \zeta - t _ {0} | = \delta_ {1}} \frac {K _ {1} ^ {\nu + \zeta \mu} (z , w) \overline {{u (w)}}}{(\zeta - t) (\zeta - t _ {0}) ^ {2}} d \zeta d ^ {2} w \right| ^ {2} d ^ {2} z\right) ^ {1 / 2}\\\leq \frac {| t - t _ {0} |}{2 \pi} \sup _ {\| u \| _ {2} = 1} \left(\iint_ {\mathbb {D}} \left(\oint_ {| \zeta - t _ {0} | = \delta_ {1}} \frac {| d \zeta |}{| \zeta - t | ^ {2} | \zeta - t _ {0} | ^ {4}}\right) \right.\\\left(\oint_ {| \zeta - t _ {0} | = \delta_ {1}} \left| \iint_ {\mathbb {D}} K _ {1} ^ {\nu + \zeta \mu} (z, w) \overline {{u (w)}} d ^ {2} w \right| ^ {2} | d \zeta |\right) d ^ {2} z\left. \right) ^ {1 / 2}\\= \frac {| t - t _ {0} |}{2 \pi} \left(\oint_ {| \zeta - t _ {0} | = \delta_ {1}} \frac {| d \zeta |}{| \zeta - t | ^ {2} | \zeta - t _ {0} | ^ {4}}\right) ^ {1 / 2} \sup _ {\| u \| _ {2} = 1} \left(\oint_ {| \zeta - t _ {0} | = \delta_ {1}} \| K _ {1} ^ {\nu + \zeta \mu} \bar {u} \| _ {2} ^ {2} | d \zeta |\right) ^ {1 / 2}.\end{array}
$$

109

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

<!-- page 119 of 136 -->

110

B. THE PERIOD MAPPING $\hat{\mathcal{P}}$

Since $\| K_{1} \| < 1$, we obtain

$$
\left| \begin{array}{c} \left\| \frac {B _ {1} (\mathrm{f} ^ {\nu + t \mu}) - B _ {1} (\mathrm{f} ^ {\nu + t _ {0} \mu})}{t - t _ {0}} - \frac {d}{d t} \Big | _ {t = t _ {0}} B _ {1} (\mathrm{f} ^ {\nu + t \mu}) \right\| \\ \leq \frac {| t - t _ {0} |}{2 \pi} \left(\oint_ {| \zeta - t _ {0} | = \delta_ {1}} \frac {| d \zeta |}{| \zeta - t | ^ {2} | \zeta - t _ {0} | ^ {4}} \oint_ {| \zeta - t _ {0} | = \delta_ {1}} | d \zeta |\right) ^ {1 / 2} \\ = O (t - t _ {0}) \quad \text {as} \quad t \to t _ {0}. \end{array} \right|
$$

To prove that $\hat{\mathcal{P}}(S) \subset \mathcal{S}_{\infty}$, we first give a characterization of the submanifold $S = \mathrm{Mob}(S^1) \backslash \mathrm{Homeo}_s(S^1)$ of $T(1)$. It has been shown by Gardiner and Sullivan [GS92] that $\beta(S) = A_{\infty}^{0}(\mathbb{D}) \cap \beta(T(1))$, where $\beta : T(1) \to A_{\infty}(\mathbb{D})$ is the Bers embedding and $A_{\infty}^{0}(\mathbb{D})$ is the subspace of the Banach space $A_{\infty}(\mathbb{D})$, defined by

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026for download from IP 130.34.46.51.

$$
A _ {\infty} ^ {0} (\mathbb {D}) = \left\{\phi \in A _ {\infty} (\mathbb {D}): \lim _ {| z | \to 1 ^ {-}} (1 - | z | ^ {2}) ^ {2} \phi (z) = 0 \right\}.
$$

Analogous to Theorem A.1 in Part I, we have the following result.

LEMMA B.2. The closure of the homogeneous space $\mathrm{Möb}(S^1)\backslash \mathrm{Diff}_+(S^1)\subset T(1)$ in the Banach manifold topology is the Banach submanifold $S$ of $T(1)$.

PROOF. For $\phi \in A_{\infty}^{0}(\mathbb{D}) \cap \beta(T(1))$, let $\phi_n = \phi \circ r_n$, where $r_n$ is the dilation $z \mapsto \frac{n}{n+1}z$, $n \in \mathbb{N}$. Since $\phi \in A_{\infty}^{0}(\mathbb{D})$, for every $\varepsilon > 0$ there exists $0 < r < 1$ such that

$$
\sup _ {r \leq | z | \leq 1} (1 - | z | ^ {2}) ^ {2} | \phi (z) | <   \frac {\varepsilon}{4}.
$$

Thus there exists $N'$ such that

$$
\sup _ {r ^ {\prime} \leq | z | \leq 1} (1 - | z | ^ {2}) ^ {2} | \phi_ {n} (z) | <   \frac {\varepsilon}{4}
$$

for $n > N'$, where $r' = \frac{1 + r}{2}$. The sequence $\{\phi_n\}$ converges uniformly to $\phi$ on compact subsets of $\mathbb{D}$, so that there exists $N''$ such that

$$
\sup _ {| z | \leq r ^ {\prime}} (1 - | z | ^ {2}) ^ {2} \left| \phi_ {n} (z) - \phi (z) \right| <   \frac {\varepsilon}{2} \quad \text {for} \quad n > N ^ {\prime \prime}.
$$

Thus $\| \phi_n - \phi \|_{\infty} < \varepsilon$ for $n > N = \max \{N', N''\}$, so that

$$
\lim _ {n \to \infty} \phi_ {n} = \phi
$$

in the $A_{\infty}(\mathbb{D})$ topology. Since $\beta(T(1))$ is open in $A_{\infty}(\mathbb{D})$, $\phi_n \in \beta(T(1))$ for large enough $n$. The functions $\phi_n$ are smooth on $S^1$ (in fact analytic), so that corresponding $\gamma_n \in \mathrm{M}\ddot{\mathrm{o}}\mathrm{b}(S^1) \backslash \mathrm{Homeo}_{qs}(S^1)$ are also smooth on $S^1$. This proves that $\overline{\mathrm{M}\ddot{\mathrm{o}}\mathrm{b}(S^1)\backslash\mathrm{Diff}_+ (S^1)} = S$.

REMARK B.3. Together with Theorem A.1 in Part I, Lemma B.2 explains the distinguished role of the embedded manifold  $\mathrm{Möb}(S^{1})\backslash\mathrm{Diff}_{+}(S^{1})\hookrightarrow T(1)$  in Teichmüller theory. Its closure in  $T(1)$  under the Banach manifold topology is the Banach submanifold S, whereas its closure under the Hilbert manifold topology is the Hilbert submanifold  $T_{0}(1)$ .

<!-- page 120 of 136 -->

B. THE PERIOD MAPPING $\hat{\mathcal{P}}$

111

THEOREM B.4. The image of the Banach submanifold $S$ under the KYNS period mapping $\hat{\mathcal{P}}: T(1) \to \mathcal{B}(\ell^2)$ is given by

$$
\left| \hat {\mathcal {P}} (S) = \mathcal {S} _ {\infty} \cap \hat {\mathcal {P}} (T (1)) \right|
$$

where $\mathcal{S}_{\infty}$ is the space of compact operators on $\ell^2$.

PROOF. It is easy to show that $\hat{\mathcal{P}}(S) \subset \mathcal{S}_{\infty}$. Indeed, by Theorem 2.6, $\hat{\mathcal{P}}(\mathrm{Mob}(S^1) \setminus \mathrm{Diff}_+(S^1)) \subset \mathcal{S}_2 \subset \mathcal{S}_{\infty}$. Since the mapping $\hat{\mathcal{P}}$ is continuous (actually, holomorphic), using Lemma B.2 proves the claim.

To prove the converse inclusion $\hat{\mathcal{P}}^{-1}(\mathcal{S}_{\infty}\cap\hat{\mathcal{P}}(T(1)))\subset S$, we use methods developed by Brazilevic in [Bra65]. Let $\mathcal{U}$ be the space of univalent functions on $\mathbb{D}$. Following [Bra65], consider the following function $\mathsf{F}:\mathcal{U}\times\mathcal{U}\times\mathbb{D}\to\mathbb{R}$,

$$
\mathsf {F} (f _ {1}, f _ {2}) (z) = \sqrt {\pi} (1 - | z | ^ {2}) \left(\iint_ {\mathbb {D}} | K _ {1} (f _ {1}) (z, w) - K _ {1} (f _ {2}) (z, w) | ^ {2} d ^ {2} w\right) ^ {1 / 2}.
$$

When $f_{1} = f$ and $f_{2} = \mathrm{id}$ — the identity mapping, we denote

$$
\mathsf {F} (f) (z) = \mathsf {F} (f, \mathrm{id}) (z) = \sqrt {\pi} (1 - | z | ^ {2}) \mathsf {K} _ {1} (z, z) ^ {1 / 2}.
$$

In [Bra65], Brazilevic has introduced a new metric on $\mathcal{U}$,

$$
d (f _ {1}, f _ {2}) = \sup _ {z \in \mathbb {D}} \mathsf {F} (f _ {1}, f _ {2}) (z),
$$

and has shown that

$$
\| \mathcal {S} (f _ {1}) - \mathcal {S} (f _ {2}) \| _ {\infty} \leq 6 d (f _ {1}, f _ {2}).
$$

For fixed $\zeta \in \mathbb{D}$, consider the kernel

$$
K _ {1} (f) (z, \zeta) = \frac {1}{\pi} \sum_ {n = 1} ^ {\infty} n \left(\sum_ {m = 1} ^ {\infty} m b _ {- n, - m} \zeta^ {m - 1}\right) z ^ {n - 1}
$$

as a holomorphic function on $\mathbb{D}$. By Grunsky inequality,

$$
\begin{array}{r l} & {\| K _ {1} (f) (\cdot , \zeta) \| _ {2} ^ {2} = \mathsf {K} _ {1} (f) (\zeta , \zeta) = \frac {1}{\pi} \sum_ {n = 1} ^ {\infty} n \left| \sum_ {m = 1} ^ {\infty} m b _ {- n, - m} \zeta^ {m - 1} \right| ^ {2}} \\ & {\qquad \leq \frac {1}{\pi} \sum_ {n = 1} ^ {\infty} n | \zeta | ^ {2 n - 2} = \frac {1}{\pi (1 - | \zeta | ^ {2}) ^ {2}} <   \infty ,} \end{array}
$$

so that $K_{1}(f)(\cdot ,\zeta)\in A_{2}^{1}(\mathbb{D})$ . For fixed $\zeta \in \mathbb{D}$ and $f_{1},f_{2}\in \mathcal{U}$ we define

$$
\psi (f _ {1}, f _ {2}; \zeta) (z) = K _ {1} (f _ {1}) (z, \zeta) - K _ {1} (f _ {2}) (z, \zeta).
$$

Then $\psi(f_1, f_2, \zeta) \in A_2^1(\mathbb{D})$. For $\psi(f_1, f_2; \zeta) \neq 0$ we set

$$
\boxed {\mathrm{u} (f _ {1}, f _ {2}; \zeta) = \frac {\psi (f _ {1} , f _ {2} ; \zeta)}{\| \psi (f _ {1} , f _ {2} ; \zeta) \| _ {2}},}
$$

and for $\psi(f_1, f_2, \zeta) = 0$ we set $\mathrm{u}(f_1, f_2; \zeta) = 0$. The following lemma generalizes Brazilevic's result [Bra65].

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026for download from IP 130.34.46.51.

LEMMA B.5. For $f_{1}, f_{2} \in \mathcal{U}$ and $z \in \mathbb{D}$,

$$
\big (1 - | z | ^ {2}) ^ {2} \left| \mathcal {S} (f _ {1}) (z) - \mathcal {S} (f _ {2}) (z) \right| \leq 6 \mathrm{F} (f _ {1}, f _ {2}) (z) \leq 6 \| K _ {1} (f _ {1}) - K _ {1} (f _ {2}) \|.
$$

<!-- page 121 of 136 -->

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

112

B. THE PERIOD MAPPING $\hat{\mathcal{P}}$

PROOF. We use the same approach as in [Bra65]. Since for $\lambda_1, \lambda_2 \in \mathrm{PSL}(2, \mathbb{C})$, $\mathcal{S}(\lambda_1 \circ f) = \mathcal{S}(f)$, $K_1(\lambda_1 \circ f) = K_1(f)$, and $\mathsf{F}(\lambda_1 \circ f_1, \lambda_2 \circ f_2)(z) = \mathsf{F}(f_1, f_2)(z)$, it is sufficient to consider only $f \in \mathcal{U}$ normalized by $f(0) = 0$ and $f'(0) = 1$. We have for fixed $z \in \mathbb{D}$,

$$
(1 - | z | ^ {2}) ^ {2} \mathcal {S} (f) (z) = \mathcal {S} (\lambda (f) _ {z} \circ f \circ \sigma_ {z}) (0)
$$

and

$$
\mathsf {F} (f _ {1}, f _ {2}) (z) = \mathsf {F} (\lambda (f _ {1}) _ {z} \circ f _ {1} \circ \sigma_ {z}, \lambda (f _ {2}) _ {z} \circ f _ {2} \circ \sigma_ {z}) (0),
$$

where $\sigma_z\in \mathrm{Mob}(S^1)$ and $\lambda (f)_z\in \mathrm{PSL}(2,\mathbb{C})$ are given by

$$
\sigma_ {z} (w) = \frac {w + z}{1 + w \bar {z}} \quad \text {and} \quad \lambda (f) _ {z} (w) = \frac {w - f (z)}{f ^ {\prime} (z) (1 - | z | ^ {2})}.
$$

Since for a normalized $f \in \mathcal{U}$ the univalent function $\lambda(f)_z \circ f \circ \sigma_z$ is also normalized, for the first inequality we need only to show that for any normalized $f \in \mathcal{U}$,

$$
| \mathcal {S} (f _ {1}) (0) - \mathcal {S} (f _ {2}) (0) | \leq 6 \mathrm{F} (f _ {1}, f _ {2}) (0).
$$

Since

$$
\mathcal {S} (f) (z) = 6 \lim _ {w \to z} \left(\frac {f ^ {\prime} (z) f ^ {\prime} (w)}{(f (z) - f (w)) ^ {2}} - \frac {1}{(z - w) ^ {2}}\right) = - 6 \sum_ {n, m = 1} ^ {\infty} n m b _ {- n, - m} z ^ {n + m - 2},
$$

we have

$$
| \mathcal {S} (f _ {1}) (0) - \mathcal {S} (f _ {2}) (0) | = 6 | b _ {- 1, - 1} (f _ {1}) - b _ {- 1, - 1} (f _ {2}) |.
$$

On the other hand, it is straightforward to compute that

$$
\begin{array}{c} \mathsf {F} (f _ {1}, f _ {2}) ^ {2} (0) = \pi \iint_ {\mathbb {D}} | K _ {1} (f _ {1}) (0, w) - K _ {1} (f _ {2}) (0, w) | ^ {2} d ^ {2} w \\ = \sum_ {m = 1} ^ {\infty} m | b _ {- 1, - m} (f _ {1}) - b _ {- 1, - m} (f _ {2}) | ^ {2}, \end{array}
$$

and the first inequality follows.

Next we observe that

$$
\mathsf {F} (f _ {1}, f _ {2}) (z) = \sqrt {\pi} \| (K _ {1} (f _ {1}) - K _ {1} (f _ {2})) \overline {{\mathrm{u} (f _ {1} , f _ {2} ; z)}} \| _ {A _ {\infty} ^ {1} (\mathbb {D})}.\tag{B.1}
$$

Indeed, by Cauchy-Schwarz inequality,

$$
\begin{array}{c} \hline \left((K _ {1} (f _ {1}) - K _ {1} (f _ {2})) \overline {{\psi (f _ {1} , f _ {2} ; z)}}\right) (w) \\ = \iint_ {\mathbb {D}} (K _ {1} (f _ {1}) (w, \zeta) - K _ {1} (f _ {2}) (w, \zeta)) \overline {{(K _ {1} (f _ {1}) (\zeta , z) - K _ {1} (f _ {2}) (\zeta , z))}} d ^ {2} \zeta \\ \leq \| \psi (f _ {1}, f _ {2}; z) \| _ {2} \| \psi (f _ {1}, f _ {2}; w) \| _ {2}, \end{array}
$$

<small><span class="docvortex-page-footnote" data-block-type="page_footnote" style="color:#6b7280">$^{1}$ Here subscript z does not denote a derivative.</span></small>

<!-- page 122 of 136 -->

B. THE PERIOD MAPPING $\hat{\mathcal{P}}$

113

with the equality for $w = z$. Hence

$$
\left| \begin{array}{c} \left\| (K _ {1} (f _ {1}) - K _ {1} (f _ {2})) \overline {{\psi (f _ {1} , f _ {2} ; z)}} \right\| _ {A _ {\infty} ^ {1} (\mathbb {D})} \\ = (1 - | z | ^ {2}) \iint_ {\mathbb {D}} | K _ {1} (f _ {1}) (\zeta , z) - K _ {1} (f _ {2}) (\zeta , z) | ^ {2}   d ^ {2} \zeta \\ = (1 - | z | ^ {2}) \| \psi (f _ {1}, f _ {2}; z) \| _ {2} ^ {2} = \mathsf {F} (f _ {1}, f _ {2}) (z) \frac {\| \psi (f _ {1} , f _ {2} ; z) \| _ {2}}{\sqrt {\pi}}. \end{array} \right|
$$

Finally, using (B.1) and the estimate in Lemma 1.3, we get

$$
\mathsf {F} (f _ {1}, f _ {2}) (z) \leq \| (K _ {1} (f _ {1}) - K _ {1} (f _ {2})) \overline {{\mathsf {u} (f _ {1} , f _ {2} ; z)}} \| _ {2} \leq \| K _ {1} (f _ {1}) - K _ {1} (f _ {2}) \|.\tag{B.2}
$$

REMARK B.6. It immediately follows from Lemma B.5 that


> **[ERRATUM B-05]** (TT:6206–6216; Lean: `remark_B_6` (Appendix/B6Completed)) **[CORRECTION 2026-10-25]** both converses are false: for `f` onto `ℂ \ {x ≥ 0, \| y \| ≤ x²}`, `‖K₁(f)‖ = d(f) = 1` while the complement has positive area (`collaboration/下属5/REMARK_B6_PROPOSAL.md`).

$$
\| \mathcal {S} (f _ {1}) - \mathcal {S} (f _ {2}) \| _ {\infty} \leq 6 d (f _ {1}, f _ {2}) \leq 6 \| K _ {1} (f _ {1}) - K _ {1} (f _ {2}) \|,
$$

which is a stronger version of Brazilevic's result [Bra65]. In case $f_{1} = f$ and $f_{2} = \mathrm{id}$ we have

$$
\| \mathcal {S} (f) \| _ {\infty} \leq 6 d (f) \leq 6 \| K _ {1} (f) \|,
$$

where $d(f) = d(f, \mathrm{id})$. Since $\| K_1(f) \| \leq 1$, where equality holds if and only if $\mathbb{C} \setminus f(\mathbb{D})$ has Lebesgue measure zero, this recovers another result in [Bra65] that $d(f) \leq 1$ for $f \in \mathcal{U}$, and $d(f) = 1$ implies that $\mathbb{C} \setminus f(\mathbb{D})$ has Lebesgue measure zero.

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

Given a normalized univalent function $f: \mathbb{D} \to \mathbb{C}$, let $f_n: \mathbb{D} \to \mathbb{C}$ be the normalized univalent function defined by $f_n = r_n^{-1} \circ f \circ r_n$, where $r_n$ is the dilation $z \mapsto \frac{n}{n+1}z$. Since $f_n$ is analytic on $S^1$, we have

$$
\lim _ {| z | \to 1 ^ {-}} (1 - | z | ^ {2}) ^ {2} \mathcal {S} (f _ {n}) (z) = 0,
$$

$$
\lim _ {| \zeta | \to 1 ^ {-}} (1 - | \zeta | ^ {2}) K _ {1} (f _ {n}) (z, \zeta) = 0,
$$

and also

$$
\lim _ {| \zeta | \to 1 ^ {-}} \left\| (1 - | \zeta | ^ {2}) K _ {1} (f _ {n}) (\cdot , \zeta) \right\| _ {2} ^ {2} = \lim _ {| \zeta | \to 1 ^ {-}} (1 - | \zeta | ^ {2}) ^ {2} K _ {1} (f _ {n}) (\zeta , \zeta) = 0.
$$

LEMMA B.7. Let $f: \mathbb{D} \to \mathbb{C}$ be a normalized univalent function and let $\{f_n\}_{n=1}^{\infty}$ be the sequence of normalized univalent functions defined above. Then

$$
\lim _ {n \to \infty} K _ {1} (f _ {n}) = K _ {1} (f)
$$

in the strong operator topology.

PROOF. For $\psi \in A_2^1 (\mathbb{D})$ set $\psi_{n} = r_{n}\circ \psi \circ r_{n}$. It is elementary to show that

$$
\lim _ {n \to \infty} \| \psi - \psi_ {n} \| _ {2} = 0.
$$

For $(K_{1}(f)\bar{\psi})_{n} = r_{n}\circ (K_{1}(f)\bar{\psi})\circ r_{n}$ we have,

$$
K _ {1} (f _ {n}) \bar {\psi} _ {n} = (K _ {1} (f) \bar {\psi}) _ {n} - r _ {n} \circ (K _ {1} (f) \bar {\psi} (1 - \chi_ {n})) \circ r _ {n},
$$

<!-- page 123 of 136 -->

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026for download from IP 130.34.46.51.

114

B. THE PERIOD MAPPING $\hat{\mathcal{P}}$

where $\chi_{n}$ is the characteristic function of the disk $\mathbb{D}_n = r_n(\mathbb{D})$. Using this identity and the inequalities $\| K_1(f)\| \leq 1$, $\| \psi_{n}\|_{2}\leq \| \psi \|_{2}$, we obtain

$$
\begin{array}{r l} & {\| (K _ {1} (f) - K _ {1} (f _ {n})) \bar {\psi} \| _ {2} \leq \| K _ {1} (f) \bar {\psi} - K _ {1} (f _ {n}) \bar {\psi} _ {n} \| _ {2} + \| K _ {1} (f _ {n}) \overline {{(\psi_ {n} - \psi)}} \| _ {2}} \\ & {\qquad \leq \| K _ {1} (f) \bar {\psi} - (K _ {1} (f) \bar {\psi}) _ {n} \| _ {2} + \| K _ {1} (f) \overline {{(\psi (1 - \chi_ {n}))}} \| _ {2} + \| \psi - \psi_ {n} \| _ {2}} \\ & {\qquad \leq \| K _ {1} (f) \bar {\psi} - (K _ {1} (f) \bar {\psi}) _ {n} \| _ {2} + \| \psi (1 - \chi_ {n}) \| _ {2} + \| \psi - \psi_ {n} \| _ {2}.} \end{array}
$$

Since $\psi \in A_2^1 (\mathbb{D})$,

$$
\varliminf_ {n \to \infty} \| \psi (1 - \chi_ {n}) \| _ {2} = 0,
$$


> **[ERRATUM B-06]** (TT:6275; Lean: `lemma_B_7`) OCR renders `lim` as `\varliminf`; the argument needs (and has) a limit. Note: the module doc cites TT:6262; the line is TT:6275.

and we get the assertion of the lemma.

LEMMA B.8. Let $\gamma = g^{-1} \circ f \in \mathcal{T}(1)$ be such that $K_1(f)$ is a compact operator. Then for every sequence $\{\zeta_m\}_{m=1}^{\infty}$ of points in $\mathbb{D}$, the corresponding sequence of functions $\{u_m\}_{m=1}^{\infty}$ in $A_2^1(\mathbb{D})$, where

$$
u _ {m} (z) = (1 - | \zeta_ {m} | ^ {2}) K _ {1} (f) (z, \zeta_ {m}), z \in \mathbb {D},
$$

contains a convergent subsequence in $A_2^1 (\mathbb{D})$.

PROOF. Consider the following sequence of functions,

$$
v _ {m} (z) = z ^ {- 2} (1 - | \zeta_ {m} | ^ {2}) K _ {3} (f) (z ^ {- 1}, \zeta_ {m}) \in A _ {2} ^ {1} (\mathbb {D}).
$$

Using the formula

$$
K _ {3} (\zeta , \zeta) + K _ {4} (\zeta , \zeta) = \frac {1}{\pi (1 - | \zeta | ^ {2}) ^ {2}},
$$

which follows from the operator identity $\mathsf{K}_3 + \mathsf{K}_4 = I$, and the inequality $\mathsf{K}_4(\zeta, \zeta) \geq 0$, we get

$$
\| v _ {m} \| _ {2} ^ {2} = (1 - | \zeta_ {m} | ^ {2}) ^ {2} \mathsf {K} _ {3} (\zeta_ {m}, \zeta_ {m}) \leq \frac {1}{\pi}.
$$

Now consider the operator $\tilde{K}_3(f):\overline{A_2^1(\mathbb{D})}\to A_2^1 (\mathbb{D})$, defined by the kernel

$$
\tilde {K} _ {3} (f) (z, w) = z ^ {- 2} K _ {3} (f) \left(z ^ {- 1}, w\right).
$$

In the standard basis for $A_2^1 (\mathbb{D})$ it is given by the matrix $B_{3}(f)$ and, therefore, is a topological isomorphism. Setting $K(f) = K_{1}(f)\tilde{K}_{3}(f)^{-1}$, we get

$$
u _ {m} = K (f) v _ {m}.
$$

Since the operator $K(f)$ is compact and the sequence $\{v_m\}_{m=1}^{\infty}$ is bounded, the statement follows.

Now we can finish the proof of the Theorem. Suppose that for $[\mu] \in T(1)$ the corresponding operator $K_1(f)$ is compact but $[\mu] \notin S$. According to Remark 1.7, this implies that there exist $\varepsilon > 0$ and a sequence $\zeta_m \in \mathbb{D}$ satisfying

$$
| \zeta_ {m} | > 1 - \frac {1}{m} \quad \text {and} \quad (1 - | \zeta_ {m} | ^ {2}) ^ {2} | \mathcal {S} (f) (\zeta_ {m}) | \geq \varepsilon .
$$

By Lemma B.8, there exists a subsequence $\zeta_{m_k}$ such that the sequence of functions

$$
u _ {m _ {k}} (z) = (1 - | \zeta_ {m _ {k}} | ^ {2}) K _ {1} (f) (z, \zeta_ {m _ {k}})
$$

converges to $u\in A_2^1 (\mathbb{D})$ in $A_2^1 (\mathbb{D})$ . Since

$$
\lim _ {| \zeta | \to 1 ^ {-}} (1 - | \zeta | ^ {2}) K _ {1} (f _ {n}) (z, \zeta) = 0,
$$

<!-- page 124 of 136 -->

B. THE PERIOD MAPPING $\hat{\mathcal{P}}$

115

for any $n\in \mathbb{N}$, the sequence of functions

$$
(1 - | \zeta_ {m _ {k}} | ^ {2}) \psi (f, f _ {n}; \zeta_ {m _ {k}}) = (1 - | \zeta_ {m _ {k}} | ^ {2}) (K _ {1} (f) (\cdot , \zeta_ {m _ {k}}) - K _ {1} (f _ {n}) (\cdot , \zeta_ {m _ {k}}))
$$

also converges to $u$ as $k \to \infty$. From Lemma B.5 and (B.2) we get the following inequality

$$
(1 - | \zeta_ {m _ {k}} | ^ {2}) ^ {2} \left| \mathcal {S} (f) (\zeta_ {m _ {k}}) - \mathcal {S} (f _ {n}) (\zeta_ {m _ {k}}) \right| \leq 6 \left\| \left(K _ {1} (f) - K _ {1} (f _ {n})\right) \overline {{\mathrm{u} (f , f _ {n} ; \zeta_ {m _ {k}})}} \right\| _ {2},
$$

which for $\psi(f, f_n, \zeta_{m_k}) = 0$ is an equality. Now passing to the limit $k \to \infty$ for fixed $n \in \mathbb{N}$, we obtain

$$
\varepsilon \leq 6 \left\| (K _ {1} (f) - K _ {1} (f _ {n})) \bar {\mathrm{u}} \right\| _ {2},
$$

where

$$
\mathrm{u} = \frac {u}{\| u \| _ {2}} \neq 0.
$$

However, according to Lemma B.7,

$$
\lim _ {n \to \infty} \| (K _ {1} (f) - K _ {1} (f _ {n}))   \bar {\mathrm{u}} \| _ {2} = 0.
$$

This contradiction proves that $[\mu] \in S$.

REMARK B.9. For $[\mu] \in S$ the proof of Lemma B.2 shows that

$$
\lim _ {n \to \infty} \mathcal {S} (f _ {n}) = \mathcal {S} (f)
$$

in $A_{\infty}(\mathbb{D})$ topology. Since the period mapping $\tilde{\mathcal{P}}$ is continuous,

$$
\lim _ {n \to \infty} K _ {1} (f _ {n}) = K _ {1} (f)
$$

in the norm topology on $\mathcal{B}(\overline{A_2^1(\mathbb{D})}, A_2^1(\mathbb{D}))$.

The following commutative diagram displays the properties of the tower of embedded manifolds $T_0(1) \hookrightarrow S \hookrightarrow T(1)$ under the KYNS period mapping $\hat{\mathcal{P}}$, the pre-Bers embedding $\hat{\beta}$ and the Bers embedding $\beta = \Psi \circ \hat{\beta}$,

$$
\mathscr {S} _ {2} (\ell^ {2}) \longrightarrow \mathscr {S} _ {\infty} (\ell^ {2}) \longrightarrow \mathscr {B} (\ell^ {2})
$$

$$
\Bigg |\begin{array}{c c c}\uparrow_ {\mathcal {P}}&&\uparrow_ {\hat {\mathcal {P}}}\\&&\uparrow_ {\hat {\mathcal {P}}}\end{array}\left. \right.
$$

$$
T _ {0} (1) \longrightarrow S \longrightarrow T (1)
$$

$$
\begin{array}{c c c} \Big \downarrow \hat {\beta} & \Big \downarrow \hat {\beta} & \Big \downarrow \hat {\beta} \end{array}
$$

$$
A _ {2} ^ {1} (\mathbb {D}) \longrightarrow A _ {\infty} ^ {1, 0} (\mathbb {D}) \longrightarrow A _ {\infty} ^ {1} (\mathbb {D})
$$

$$
\Bigg \downarrow \Psi \quad \quad \quad \Bigg \downarrow \Psi \quad \quad \quad \Bigg \downarrow \Psi
$$

$$
A _ {2} (\mathbb {D}) \longrightarrow A _ {\infty} ^ {(0)} (\mathbb {D}) \longrightarrow A _ {\infty} (\mathbb {D})
$$

Here $A_{\infty}^{1,0}(\mathbb{D})$ is the closed subspace of $A_{\infty}^{1}(\mathbb{D})$, defined by

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026for download from IP 130.34.46.51.

$$
A _ {\infty} ^ {1, 0} (\mathbb {D}) = \left\{\psi \in A _ {\infty} ^ {1} (\mathbb {D}): \lim _ {| z | \to 1 ^ {-}} (1 - | z | ^ {2}) \psi (z) = 0 \right\}.
$$

All horizontal maps are embeddings, and all vertical maps are holomorphic mappings of Banach and Hilbert manifolds respectively. All these properties have been

<!-- page 125 of 136 -->

116

B. THE PERIOD MAPPING $\hat{\mathcal{P}}$

proved already, except for the simple fact $\Psi(A_{\infty}^{1,0}(\mathbb{D})) \subset A_{\infty}^{0}(\mathbb{D})$, which easily follows from Cauchy integral formula.

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

<!-- page 126 of 136 -->

## Bibliography

[AB60] Lars Ahlfors and Lipman Bers, Riemann's mapping theorem for variable metrics, Ann. of Math. (2) 72 (1960), 385-404.

[Ahl61] Lars V. Ahlfors, Some remarks on Teichmüller's space of Riemann surfaces, Ann. of Math. (2) 74 (1961), 171–191.

[Ahl62] \_\_\_\_, Curvature properties of Teichmüller's space, J. Analyse Math. 9 (1961/1962), 161–176.

[Ahl87] \_\_\_\_, Lectures on quasiconformal mappings, Wadsworth & Brooks/Cole Advanced Books & Software, Monterey, CA, 1987, With the assistance of Clifford J. Earle, Jr., Reprint of the 1966 original.

[Ber65] L Bers, Automorphic forms and general Teichmüller spaces, Proc. Conf. Complex Analysis (Minneapolis, 1964), Springer, Berlin, 1965, pp. 109–113.

[Ber66] Lipman Bers, A non-standard integral equation with applications to quasiconformal mappings, Acta Math. 116 (1966), 113-134.

[Ber72] \_\_\_\_, Uniformization, moduli and Kleinian groups, Bull. London. Math. Soc. 4 (1972), 257–300.

[Ber73] \_\_\_\_, Fiber spaces over Teichmüller spaces, Acta. Math. 130 (1973), 89–126.

[BFK92] D. Burghelea, L. Friedlander, and T. Kappeler, Meyer-Vietoris type formula for determinants of elliptic differential operators, J. Funct. Anal. 107 (1992), no. 1, 34–65.

[Bou67] N. Bourbaki, Éléments de mathématique. Fasc. XXXIII. Variétés différentielles et analytiques. Fascicule de résultats (Paragraphes 1 à 7), Actualités Scientifiques et Industrielles, No. 1333, Hermann, Paris, 1967.

[BP78] Jochen Becker and Christian Pommerenke, Über die quasikonforme Fortsetzung schlichter Funktionen, Math. Z. 161 (1978), no. 1, 69–80.

[BR87a] M. J. Bowick and S. G. Rajeev, The holomorphic geometry of closed bosonic string theory and Diff $S^1 / S^1$, Nuclear Phys. B 293 (1987), no. 2, 348-384.

[BR87b] \_\_\_\_, String theory as the Kähler geometry of loop space, Phys. Rev. Lett. 58 (1987), no. 6, 535–538.

[Bra65] J. E. Brazilevič, On dispersion of coefficients of univalent functions, Mat. Sb. (N.S.) 68(110) (1965), 549–560.

[DE86] Adrien Douady and Clifford J. Earle, Conformally natural extension of homeomorphisms of the circle, Acta Math. 157 (1986), no. 1-2, 23-48.

[Dur83] P. L. Duren, Univalent functions, Grundlehren der Mathematischen Wissenschaften [Fundamental Principles of Mathematical Sciences], vol. 259, Springer-Verlag, New York, 1983.

[EN88] Clifford J. Earle and Subhashis Nag, Conformally natural reflections in Jordan curves with applications to Teichmüller spaces, Holomorphic functions and moduli, Vol. II (Berkeley, CA, 1986), Math. Sci. Res. Inst. Publ., vol. 11, Springer, New York, 1988, pp. 179–194.

[GK69] I. C. Gohberg and M. G. Krein, Introduction to the theory of linear nonselfadjoint operators, Translated from the Russian by A. Feinstein. Translations of Mathematical Monographs, Vol. 18, American Mathematical Society, Providence, R.I., 1969.

[GS92] Frederick P. Gardiner and Dennis P. Sullivan, Symmetric structures on a closed curve, Amer. J. Math. 114 (1992), no. 4, 683-736.

[Ham02] D. H. Hamilton, Conformal welding, Handbook of complex analysis: geometric function theory, Vol. 1, North-Holland, Amsterdam, 2002, pp. 137–146.

[Hej76] Dennis A. Hejhal, The Selberg trace formula for $\mathrm{PSL}(2,R)$. Vol. I, Springer-Verlag, Berlin, 1976, Lecture Notes in Mathematics, Vol. 548.

117

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

<!-- page 127 of 136 -->

118

BIBLIOGRAPHY

[Hum72] J. A. Hummel, Inequalities of Grunsky type for Aharonov pairs, J. Analyse Math. 25 (1972), 217-257.

[HZ99] Andrew Hassell and Steve Zelditch, Determinants of Laplacians in exterior domains, Internat. Math. Res. Notices (1999), no. 18, 971–1004.

[Kir87] A. A. Kirillov, Kähler structure on the K-orbits of a group of diffeomorphisms of the circle, Funktsional. Anal. i Prilozhen. 21 (1987), no. 2, 42–45.

[KY87] A. A. Kirillov and D. V. Yur'ev, Kähler geometry of the infinite-dimensional homogeneous space  $M = \text{diff}_{+}(S^{1})/\text{rot}(S^{1})$ , Funktsional. Anal. i Prilozhen. 21 (1987), no. 4, 35–46.

[KY88] A. A. Kirillov and D. V. Yuriev, Representations of the Virasoro algebra by the orbit method, J. Geom. Phys. 5 (1988), no. 3, 351-363.

[Lan85] Serge Lang, $\mathrm{SL}_2(\mathbf{R})$, Graduate Texts in Mathematics, vol. 105, Springer-Verlag, New York, 1985, Reprint of the 1975 edition.

[Lan95] \_\_\_\_, Differential and Riemannian manifolds, third ed., Springer-Verlag, New York, 1995.

[Leh87] Olli Lehto, Univalent functions and Teichmüller spaces, Springer-Verlag, New York, 1987.

[Nag88] Subhashis Nag, The complex analytic theory of Teichmüller spaces, John Wiley & Sons Inc., New York, 1988, A Wiley-Interscience Publication.

[Nag92] \_\_\_\_, A period mapping in universal Teichmüller space, Bull. Amer. Math. Soc. (N.S.)
26 (1992), no. 2, 280–287.

[NS95] Subhashis Nag and Dennis Sullivan, Teichmüller theory and the universal period mapping via quantum calculus and the  $H^{1/2}$  space on the circle, Osaka J. Math. 32 (1995), no. 1, 1–34.

[NV90] Subhashis Nag and Alberto Verjovsky, diff( $S^1$ ) and the Teichmüller spaces, Comm. Math. Phys. 130 (1990), no. 1, 123-138.

[Pat75] S. J. Patterson, A lattice-point problem in hyperbolic space, Mathematika 22 (1975), no. 1, 81–88.

[Pom92] Ch. Pommerenke, Boundary behaviour of conformal maps, Springer-Verlag, Berlin, 1992.

[PS86] Andrew Pressley and Graeme Segal, Loop groups, Oxford Mathematical Monographs, The Clarendon Press Oxford University Press, New York, 1986.

[Roy75] H. L. Royden, Intrinsic metrics on Teichmüller space, Proceedings of the International Congress of Mathematicians (Vancouver, B. C., 1974), Vol. 2, Canad. Math. Congress, Montreal, Que., 1975, pp. 217–221.

[Sch57] M. Schiffer, The Fredholm eigen values of plane domains, Pacific J. Math. 7 (1957), 1187-1225.

[Sch59] \_\_\_\_, Fredholm eigen values of multiply-connected domains, Pacific J. Math. 9 (1959), 211–269.

[Sch81] Menahem Schiffer, Fredholm eigenvalues and Grunsky matrices, Ann. Polon. Math. 39 (1981), 149–164.

[Seg81] Graeme Segal, Unitary representations of some infinite-dimensional groups, Comm. Math. Phys. 80 (1981), no. 3, 301–342.

[SH62] M. Schiffer and N. S. Hawley, Connections and conformal mapping, Acta Math. 107 (1962), 175–274.

[Sie64] Carl Ludwig Siegel, Symplectic geometry, Academic Press, New York, 1964.

[STZ99] Maria E. Schonbek, Andrey N. Todorov, and Jorge P. Zubelli, Geodesic flows on diffeomorphisms of the circle, Grassmannians, and the geometry of the periodic KdV equation, Adv. Theor. Math. Phys. 3 (1999), no. 4, 1027–1092.

[SW85] Graeme Segal and George Wilson, Loop groups and equations of KdV type, Inst. Hautes Études Sci. Publ. Math. (1985), no. 61, 5–65.

[Teo03] Lee-Peng Teo, Analytic functions and integrable hierarchies—characterization of tau functions, Lett. Math. Phys. 64 (2003), no. 1, 75–92.

[Teo04] \_\_\_\_, The Velling-Kirillov metric on the universal Teichmüller curve, J. Analyse Math. 93 (2004), 271–308.

[TT03] Leon A. Takhtajan and Lee-Peng Teo, Liouville action and Weil-Petersson metric on deformation spaces, global Kleinian reciprocity and holography, Comm. Math. Phys. 239 (2003), no. 1-2, 183–240.

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

<!-- page 128 of 136 -->

BIBLIOGRAPHY

119

[TZ91] L. A. Takhtajan and P. G. Zograf, A local index theorem for families of  $\bar{\partial}$ -operators on punctured Riemann surfaces and a new Kähler metric on their moduli spaces, Comm. Math. Phys. 137 (1991), no. 2, 399–426.

[Vel] John A. Velling, A projectively natural metric on Teichmüller's spaces, unpublished manuscript.

[Wol86] Scott A. Wolpert, Chern forms and the Riemann tensor for the moduli space of curves, Invent. Math. 85 (1986), no. 1, 119–145.

[YB53] K. Yano and S. Bochner, Curvature and Betti numbers, Annals of Mathematics Studies, No. 32, Princeton University Press, Princeton, N. J., 1953.

[ZT87] P. G. Zograf and L. A. Takhtadzhyan, A local index theorem for families of  $\overline{\partial}$ -operators on Riemann surfaces, Uspekhi Mat. Nauk 42 (1987), no. 6(258), 133–150.

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

<!-- page 129 of 136 -->

This page intentionally left blank

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

<!-- page 130 of 136 -->

## Editorial Information

To be published in the Memoirs, a paper must be correct, new, nontrivial, and significant. Further, it must be well written and of interest to a substantial number of mathematicians. Piecemeal results, such as an inconclusive step toward an unproved major theorem or a minor variation on a known result, are in general not acceptable for publication. Papers appearing in Memoirs are generally at least 80 and not more than 200 published pages in length. Papers less than 80 or more than 200 published pages require the approval of the Managing Editor of the Transactions/Memoirs Editorial Board.

As of May 31, 2006, the backlog for this journal was approximately 11 volumes. This estimate is the result of dividing the number of manuscripts for this journal in the Providence office that have not yet gone to the printer on the above date by the average number of monographs per volume over the previous twelve months, reduced by the number of volumes published in four months (the time necessary for preparing a volume for the printer). (There are 6 volumes per year, each containing at least 4 numbers.)

A Consent to Publish and Copyright Agreement is required before a paper will be published in the Memoirs. After a paper is accepted for publication, the Providence office will send a Consent to Publish and Copyright Agreement to all authors of the paper. By submitting a paper to the Memoirs, authors certify that the results have not been submitted to nor are they under consideration for publication by another journal, conference proceedings, or similar publication.

## Information for Authors

Memoirs are printed from camera copy fully prepared by the author. This means that the finished book will look exactly like the copy submitted.

The paper must contain a descriptive title and an abstract that summarizes the article in language suitable for workers in the general field (algebra, analysis, etc.). The descriptive title should be short, but informative; useless or vague phrases such as “some remarks about” or “concerning” should be avoided. The abstract should be at least one complete sentence, and at most 300 words. Included with the footnotes to the paper should be the 2000 Mathematics Subject Classification representing the primary and secondary subjects of the article. The classifications are accessible from www.ams.org/msc/. The list of classifications is also available in print starting with the 1999 annual index of Mathematical Reviews. The Mathematics Subject Classification footnote may be followed by a list of key words and phrases describing the subject matter of the article and taken from it. Journal abbreviations used in bibliographies are listed in the latest Mathematical Reviews annual index. The series abbreviations are also accessible from www.ams.org/publications/. To help in preparing and verifying references, the AMS offers MR Lookup, a Reference Tool for Linking, at www.ams.org/mrlookup/. When the manuscript is submitted, authors should supply the editor with electronic addresses if available. These will be printed after the postal address at the end of the article.

Electronically prepared manuscripts. The AMS encourages electronically prepared manuscripts, with a strong preference for $\mathcal{A}_{\mathsf{MS}}$-LATEX. To this end, the Society has prepared $\mathcal{A}_{\mathsf{MS}}$-LATEX author packages for each AMS publication. Author packages include instructions for preparing electronic manuscripts, the AMS Author Handbook, samples, and a style file that generates the particular design specifications of that publication series. Though $\mathcal{A}_{\mathsf{MS}}$-LATEX is the highly preferred format of TEX, author packages are also available in $\mathcal{A}_{\mathsf{MS}}$-TEX.

Authors may retrieve an author package from e-MATH starting from www.ams.org/tex/ or via FTP to ftp.ams.org (login as anonymous, enter username as password, and type cd pub/author-info). The AMS Author Handbook and the Instruction Manual are available in PDF format following the author packages link from www.ams.org/tex/. The author package can also be obtained free of charge by sending

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

<!-- page 131 of 136 -->

email to tech-support@ams.org (Internet) or from the Publication Division, American Mathematical Society, 201 Charles St., Providence, RI 02904-2294, USA. When requesting an author package, please specify $\mathcal{A}_{\mathsf{MS}}$-IATEX or $\mathcal{A}_{\mathsf{MS}}$-TEX and the publication in which your paper will appear. Please be sure to include your complete mailing address.

Sending electronic files. After acceptance, the source file(s) should be sent to the Providence office (this includes any TEX source file, any graphics files, and the DVI or PostScript file).

Before sending the source file, be sure you have proofread your paper carefully. The files you send must be the EXACT files used to generate the proof copy that was accepted for publication. For all publications, authors are required to send a printed copy of their paper, which exactly matches the copy approved for publication, along with any graphics that will appear in the paper.

TEX files may be submitted by email, FTP, or on diskette. The DVI file(s) and PostScript files should be submitted only by FTP or on diskette unless they are encoded properly to submit through email. (DVI files are binary and PostScript files tend to be very large.)

Electronically prepared manuscripts can be sent via email to pub-submit@ams.org (Internet). The subject line of the message should include the publication code to identify it as a Memoir. T $_{EX}$ source files, DVI files, and PostScript files can be transferred over the Internet by FTP to the Internet node e-math.ams.org (130.44.1.100).

Electronic graphics. Comprehensive instructions on preparing graphics are available at www.ams.org/jourhtml/graphics.html. A few of the major requirements are given here.

Submit files for graphics as EPS (Encapsulated PostScript) files. This includes graphics originated via a graphics application as well as scanned photographs or other computer-generated images. If this is not possible, TIFF files are acceptable as long as they can be opened in Adobe Photoshop or Illustrator. No matter what method was used to produce the graphic, it is necessary to provide a paper copy to the AMS.

Authors using graphics packages for the creation of electronic art should also avoid the use of any lines thinner than 0.5 points in width. Many graphics packages allow the user to specify a “hairline” for a very thin line. Hairlines often look acceptable when proofed on a typical laser printer. However, when produced on a high-resolution laser imagesetter, hairlines become nearly invisible and will be lost entirely in the final printing process.

Screens should be set to values between $15\%$ and $85\%$. Screens which fall outside of this range are too light or too dark to print correctly. Variations of screens within a graphic should be no less than $10\%$.

Inquiries. Any inquiries concerning a paper that has been accepted for publication should be sent directly to the Electronic Prepress Department, American Mathematical Society, 201 Charles St., Providence, RI 02904, USA.

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

<!-- page 132 of 136 -->

## Editors

This journal is designed particularly for long research papers, normally at least 80 pages in length, and groups of cognate papers in pure and applied mathematics. Papers intended for publication in the Memoirs should be addressed to one of the following editors. In principle the Memoirs welcomes electronic submissions, and some of the editors, those whose names appear below with an asterisk (\*), have indicated that they prefer them. However, editors reserve the right to request hard copies after papers have been submitted electronically. Authors are advised to make preliminary email inquiries to editors about whether they are likely to be able to handle submissions in a particular electronic form.

\*Algebra to ALEXANDER KLESHCHEV, Department of Mathematics, University of Oregon, Eugene, OR 97403-1222; email: ams@noether.uoregon.edu

Algebra and its application to MINA TEICHER, Emmy Noether Research Institute for Mathematics, Bar-Ilan University, Ramat-Gan 52900, Israel; email: teicher@macs.biu.ac.il

Algebraic geometry to DAN ABRAMOVICH, Department of Mathematics, Brown University, Box 1917, Providence, RI 02912; email: amsedit@math.brown.edu

\*Algebraic number theory to V. KUMAR MURTY, Department of Mathematics, University of Toronto, 100 St. George Street, Toronto, ON M5S 1A1, Canada; email: murty@math.toronto.edu

\*Algebraic topology to ALEJANDRO ADEM, Department of Mathematics, University of British Columbia, Room 121, 1984 Mathematics Road, Vancouver, British Columbia, Canada V6T 1Z2; email: adem@math.ubc.ca

\*Combinatorics to JOHN R. STEMBRIDGE, Department of Mathematics, University of Michigan, Ann Arbor, Michigan 48109-1109; email: FRS@umich.edu

Complex analysis and harmonic analysis to ALEXANDER NAGEL, Department of Mathematics, University of Wisconsin, 480 Lincoln Drive, Madison, WI 53706-1313; email: nagel@math.wisc.edu

\* Differential geometry and global analysis to LISA C. JEFFREY, Department of Mathematics, University of Toronto, 100 St. George St., Toronto, ON Canada M5S 3G3; email: jeffrey@math.toronto.edu

Dynamical systems and ergodic theory to AMIE WILKINSON, Department of Mathematics, Northwestern University, 2033 Sheridan Road, Evanston, IL 60208-2730; email: transactions@math.northwestern.edu

\*Functional analysis and operator algebras to MARIUS DADARLAT, Department of Mathematics, Purdue University, 150 N. University St., West Lafayette, IN 47907-2067; email: mdd@math.purdue.edu

\*Geometric analysis to TOBIAS COLDING, Courant Institute, New York University, 251 Mercer St., New York, NY 10012; email: traneditor@cims.nyu.edu

\*Geometric analysis to MLADEN BESTVINA, Department of Mathematics, University of Utah, 155 South 1400 East, JWB 233, Salt Lake City, Utah 84112-0090; email: bestvina@math.utah.edu

Harmonic analysis, representation theory, and Lie theory to ROBERT J. STANTON, Department of Mathematics, The Ohio State University, 231 West 18th Avenue, Columbus, OH 43210-1174; email:stanton@math.ohio-state.edu

\*Logic to STEFFEN LEMPP, Department of Mathematics, University of Wisconsin, 480 Lincoln Drive, Madison, Wisconsin 53706-1388; email: lempp@math.wisc.edu

\*Ordinary differential equations, and applied mathematics to PETER W. BATES, Department of Mathematics, Michigan State University, East Lansing, MI 48824-1027; email: bates@math.msu.edu

\* Partial differential equations to GUSTAVO PONCE, Department of Mathematics, South Hall, Room 6607, University of California, Santa Barbara, CA 93106; email: ponce@math.ucsb.edu

\*Probability and statistics to KRZYSZTOF BURDZY, Department of Mathematics, University of Washington, Box 354350, Seattle, Washington 98195-4350; email: burdzy@math.washington.edu

\*Real analysis and partial differential equations to DANIEL TATARU, Department of Mathematics, University of California, Berkeley, Berkeley, CA 94720; email: tataru@math.berkeley.edu

All other communications to the editors should be addressed to the Managing Editor, ROBERT GURALNICK, Department of Mathematics, University of Southern California, Los Angeles, CA 90089-1113; email: guralnic@math.usc.edu.

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

<!-- page 133 of 136 -->

This page intentionally left blank

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

<!-- page 134 of 136 -->

Titles in This Series

864 John M. Lee, Fredholm operators and Einstein metrics on conformally compact manifolds, 2006

863 M. Lübke and A. Teleman, The universal Kobayashi-Hitchin correspondence on Hermitian manifolds, 2006

862 Alberto Canonaco, The Beilinson complex and canonical rings of irregular surfaces, 2006

861 Leon A. Takhtajan and Lee-Peng Teo, Weil-Petersson metric on the universal Teichmüller space, 2006

860 Thomas M. Fiore, Pseudo limits, biadjoints and pseudo algebras: Categorical foundations of conformal field theory, 2006

859 N. Arcozzi, R. Rochberg, and E. Sawyer, Carleson measures and interpolating sequences for Besov spaces on complex balls, 2006

858 Enrico Valdinoci, Berardino Sciunzi, and Vasile Ovidiu Savin, Flat level set regularity of $p$-Laplace phase transitions, 2006

857 Donatella Danielli, Nocola Garofalo, and Duy-Minh Nhieu, Non-doubling Ahlfors measures, perimeter measures, and the characterization of the trace spaces of Sobolev functions in Carnot-Carathéodory spaces, 2006

856 Vladimir Bolotnikov and Harry Dym, On boundary interpolation for matrix valued Schur functions, 2006

855 Yevgenia Kashina, Yorck Sommerhäuser, and Yongchang Zhu, On higher Frobenius-Schur indicators, 2006

854 Noam Greenberg, The role of true finiteness in the admissible recursively enumerable degrees, 2006

853 Joachim Krieger, Stability of spherically symmetric wave maps, 2006

852 Viorel Barbu, Irena Lasiecka, and Roberto Triggiani, Tangential boundary stabilization of Navier-Stokes equations, 2006

851 Jie Wu, On maps from loop suspensions to loop spaces and the shuffle relations on the Cohen groups, 2006

850 Siegfried Echterhoff, S. Kaliszewski, John Quigg, and Iain Raeburn, A categorical approach to imprimitivity theorems for $C^*$-dynamical systems, 2006

849 Katsuhiko Kuribayashi, Mamoru Mimura, and Tetsu Nishimoto, Twisted tensor products related to the cohomology of the classifying spaces of loop groups, 2006

848 Bob Oliver, Equivalences of classifying spaces completed at the prime two, 2006

847 Eric T. Sawyer and Richard L. Wheeden, Hölder continuity of weak solutions to subelliptic equations with rough coefficients, 2006

846 Victor Beresnevich, Detta Dickinson, and Sanju Velani, Measure theoretic laws for lim-sup sets, 2006

845 Ehud Friedgut, Vojtech Rödl, Andrzej Ruciński, and Prasad V. Tetali, A Sharp threshold for random graphs with a monochromatic triangle in every edge coloring, 2006

844 Amadeu Delshams, Rafael de la Llave, and Tere M. Seara, A geometric mechanism for diffusion in Hamiltonian systems overcoming the large gap problem: Heuristics and rigorous verification on a model, 2006

843 Denis V. Osin, Relatively hyperbolic groups: Intrinsic geometry, algebraic properties, and algorithmic problems, 2006

842 David P. Blecher and Vrej Zarikian, The calculus of one-sided $M$-ideals and multipliers in operator spaces, 2006

841 Enrique Artal Bartolo, Pierrette Cassou-Noguès, Ignacio Luengo, and Alejandro Melle Hernández, Quasi-ordinary power series and their zeta functions, 2005

840 Sławomir Kołodziej, The complex Monge-Ampère equation and pluripotential theory, 2005

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

<!-- page 135 of 136 -->

TITLES IN THIS SERIES

839 Mihai Ciucu, A random tiling model for two dimensional electrostatics, 2005

838 V. Jurdjevic, Integrable Hamiltonian systems on complex Lie groups, 2005

837 Joseph A. Ball and Victor Vinnikov, Lax-Phillips scattering and conservative linear systems: A Cuntz-algebra multidimensional setting, 2005

836 H. G. Dales and A. T.-M. Lau, The second duals of Beurling algbras, 2005

835 Kiyoshi Igusa, Higher complex torsion and the framing principle, 2005

834 Keníchi Ohshika, Kleinian groups which are limits of geometrically finite groups, 2005

833 Greg Hjorth and Alexander S. Kechris, Rigidity theorems for actions of product groups and countable Borel equivalence relations, 2005

832 Lee Klingler and Lawrence S. Levy, Representation type of commutative Noetherian rings III: Global wildness and tameness, 2005

831 K. R. Goodearl and F. Wehrung, The complete dimension theory of partially ordered systems with equivalence and orthogonality, 2005

830 Jason Fulman, Peter M. Neumann, and Cheryl E. Praeger, A generating function approach to the enumeration of matrices in classical groups over finite fields, 2005

829 S. G. Bobkov and B. Zegarlinski, Entropy bounds and isoperimetry, 2005

828 Joel Berman and Paweł M. Idziak, Generative complexity in algebra, 2005

827 Trevor A. Welsh, Fermionic expressions for minimal model Virasoro characters, 2005

826 Guy Métivier and Kevin Zumbrun, Large viscous boundary layers for noncharacteristic nonlinear hyperbolic problems, 2005

825 Yaozhong Hu, Integral transformations and anticipative calculus for fractional Brownian motions, 2005

824 Luen-Chau Li and Serge Parmentier, On dynamical Poisson groupoids I, 2005

823 Claus Mokler, An analogue of a reductive algebraic monoid whose unit group is a Kac-Moody group, 2005

822 Stefano Pigola, Marco Rigoli, and Alberto G. Setti, Maximum principles on Riemannian manifolds and applications, 2005

821 Nicole Bopp and Hubert Rubenthaler, Local zeta functions attached to the minimal spherical series for a class of symmetric spaces, 2005

820 Vadim A. Kaimanovich and Mikhail Lyubich, Conformal and harmonic measures on laminations associated with rational maps, 2005

819 F. Andreatta and E. Z. Goren, Hilbert modular forms: Mod $p$ and $p$-adic aspects, 2005

818 Tom De Medts, An algebraic structure for Moufang quadrangles, 2005

817 Javier Fernández de Bobadilla, Moduli spaces of polynomials in two variables, 2005

816 Francis Clarke, Necessary conditions in dynamic optimization, 2005

815 Martin Bendersky and Donald M. Davis,  $V_{1}$ -periodic homotopy groups of  $SO(n)$ , 2004

814 Johannes Huebschmann, Kähler spaces, nilpotent orbits, and singular reduction, 2004

813 Jeff Groah and Blake Temple, Shock-wave solutions of the Einstein equations with perfect fluid sources: Existence and consistency by a locally inertial Glimm scheme, 2004

812 Richard D. Canary and Darryl McCullough, Homotopy equivalences of 3-manifolds and deformation theory of Kleinian groups, 2004

811 Ottmar Loos and Erhard Neher, Locally finite root systems, 2004

810 W. N. Everitt and L. Markus, Infinite dimensional complex symplectic spaces, 2004

For a complete list of titles in this series, visit the AMS Bookstore at www.ams.org/bookstore/.

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.

<!-- page 136 of 136 -->

ISBN 0-8218-3936-5 9780821839362

MEMO/183/861

AMS on the Web
www.ams.org

Licensed to Tohoku University. Prepared on Thu Oct 22 22:57:39 EDT 2026 for download from IP 130.34.46.51.