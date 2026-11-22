#set document(title: "A four-point proof of the Pythagorean theorem")
#set page(paper: "us-letter", margin: (x: 0.82in, top: 0.66in, bottom: 0.72in),
  numbering: "1", number-align: center)
#set text(font: "Charter", size: 11.8pt, fill: rgb("#20292a"))
#set par(leading: 0.55em, justify: false)
#set block(spacing: 0.70em)
#set heading(numbering: none)
#show heading.where(level: 1): it => block(above: 0pt, below: 12pt)[
  #text(size: 24pt, weight: "bold", it.body)]
#show heading.where(level: 2): it => block(above: 10pt, below: 5pt)[
  #text(size: 14pt, weight: "bold", it.body)]
#show math.equation.where(block: true): set block(above: 6pt, below: 6pt)

= A four-point proof of the Pythagorean theorem

Let $a$ and $b$ be the legs of a right triangle and $c$ its hypotenuse. We will prove $a^2+b^2=c^2$ by comparing how three areas change when their common vertex moves.

#grid(columns: (1fr, 1.05fr), gutter: 18pt, align: (left, horizon),
  [
    *Construction.* Draw the triangle with leg $a$ horizontal and leg $b$ vertical. Let $I$ be its incenter, the point where the angle bisectors meet. Center a small square at $I$, entirely inside the triangle. Place one diagonal along the bisector between $a$ and $c$.

    Join $I$ to the three triangle vertices. Then move $I$ to a corner $P$ of the square and draw the three joins again.
  ],
  [#image("four-point-proof.svg", width: 100%)
   #align(center)[#text(size: 9.3pt, style: "italic")[The three pieces for one choice of $P$.]]])

== What moving the vertex changes

Let $x$, $y$, and $z$ be the signed changes in the distances to the lines containing $b$, $a$, and $c$, respectively. A change is positive when $P$ is farther from the line than $I$ was. Each piece has area equal to half its base times its height. Since the three pieces still fill the same triangle, their area changes sum to zero. Doubling gives
$ b x + a y + c z = 0. $

Let $P$ visit all four corners. In what follows, each sum runs over those four visits.

*Reflection.* The chosen diagonal is a mirror for the square. Reflecting in it fixes $I$, exchanges the lines containing $a$ and $c$, and permutes the four corners. Hence the four $y$ readings are the four $z$ readings in another order.

*Quarter-turn.* In axes pointing inward from the two legs, $(x,y)$ is the displacement from $I$ to $P$. A quarter-turn takes $(x,y)$ to $(-y,x)$ and permutes the corners. Thus $sum x^2 = sum y^2$. It also negates $x y$, so $sum x y=0$.

Write $K = sum x^2 = sum y^2 = sum z^2$. At least one corner has a different horizontal coordinate from $I$, so $K>0$. Squaring $c z=-(b x+a y)$ and summing now gives
$ c^2 K = b^2 sum x^2 + 2 a b sum x y + a^2 sum y^2 = (a^2+b^2)K. $
Dividing by $K$ proves $a^2+b^2=c^2$. #h(0.25em) $square.stroked.small$

#pagebreak()

= How the Lean proof measures length

The geometric proof is complete on the first page. The Lean file constructs the required reflection in coordinates before measuring the hypotenuse.

== The ruler and its mirror

For this calculation, take the acute vertex where $a$ meets $c$ as the origin, with the first axis pointing along $a$ toward the right angle. The vertices then have coordinates $(0,0)$, $(a,0)$, and $(a,b)$. Write $L(X,Y)$ for the measured length of a segment from the origin to $(X,Y)$. The formal proof uses two properties of this measurement.

+ A point $(r,0)$ at a nonnegative ruler marking has length $r$.
+ Reflecting a point in a line through the origin preserves its measured length.

To read $L(a,b)$, fold $(a,b)$ onto a ruler marking $(c,0)$. If the mirror is the line $Y=t X$, a direction along it is $(1,t)$ and a perpendicular direction is $(-t,1)$ by a quarter-turn. The segment joining the two points must be perpendicular to the mirror, and its midpoint must lie on the mirror. These conditions give, respectively,
$ a-c=-t b, quad b=t(a+c). $

Substituting $c=a+b t$ into the second condition gives $f(t)=b t^2+2a t-b=0$. Since $f(0)=-b<0$ and $f(1)=2a>0$, there is a root between 0 and 1. For that root, $c=a+b t>0$ and both mirror conditions hold. The ruler therefore reads $L(a,b)=c$. The Lean file proves the required root exists from the least-upper-bound property of the scalar field.

== The four readings in coordinates

Use $(1,t)$ for a displacement along the square’s diagonal. A sufficiently small common scale puts all four corners inside the triangle. We omit that scale because every height change is proportional to it. In these axes the signed changes above the vertical and horizontal legs are $-X$ and $Y$. The hypotenuse reading $Z$ is the vertical displacement of the reflected corner.

#align(center)[#table(columns: 5, align: center, inset: (x: 13pt, y: 3pt),
  stroke: none, table.hline(stroke: 0.6pt + rgb("#829993")),
  [Corner], [1], [2], [3], [4],
  table.hline(stroke: 0.4pt + rgb("#aebcb9")),
  [$X$], [$1$], [$-t$], [$-1$], [$t$],
  [$Y$], [$t$], [$1$], [$-t$], [$-1$],
  [$Z$], [$t$], [$-1$], [$-t$], [$1$],
  table.hline(stroke: 0.6pt + rgb("#829993")))]

The area equation is $b X-a Y=c Z$. For corners 1 and 2 it reads $b-a t=c t$ and $-b t-a=-c$, exactly the two mirror conditions above. The opposite corners reverse all signs. Lean squares and sums these four equations, cancels the mixed term, and divides by the positive common sum as on page one.

#text(size: 10pt)[*Formal statement.* In #raw("FourPoint.lean"), #raw("FourPoint.pythagoras_lengths") proves $L(a,0)^2+L(0,b)^2=L(a,b)^2$ for all $a,b>0$ over a complete ordered field with the stated ruler and reflection properties. Run #raw("lean FourPoint.lean") with Lean 4.35.0.]
