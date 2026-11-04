# Eight opposite sources and two nonreverse adjacent classes

**Status: elementary proof.** This uses the proved nine-opposite
theorem; it does not use the finite eight-cube verification.

**Lemma.** Take eight opposite sources, each variety occurring at most
twice. Add two adjacent sources whose tricolour classes are neither
equal nor reverses of one another. An opposite target can be assembled.

## 1. The corners at which one additional source suffices

Suppose the eight opposite sources do not already assemble. For each
opposite target \(T\), let

\[
E_T=\{c\in T:\text{the eight sources can fill all seven positions of }
T\setminus\{c\}\}.
\]

Let \(E\) be the union of these sets over all opposite targets.
Every \(E_T\), and hence \(E\), is invariant under reversal of
corner directions: reversing the directions in a partial matching
preserves compatibility of every opposite source. Thus \(E\) is
the bidirected version of a graph \(B\) on the five colours.

Any additional source meeting \(E\) completes an opposite target:
put it at the relevant corner \(c\), then use the seven-position
matching defining \(c\in E_T\).

## 2. The graph B contains two adjacent edges

Suppose \(B\) were a matching. On five vertices it would have at
most two edges. At least five opposite varieties avoid those edges:
two fixed edges are avoided by exactly five varieties, and a smaller
edge set has more avoiders. Among eight source copies, at most four
varieties can be doubled. Choose an avoiding variety \(R\) that is
not doubled.

Adding \(R\) gives nine opposite sources with multiplicity cap two,
so the nine-opposite theorem supplies an assembly. The assembly must
use \(R\), since the original core did not assemble. If \(R\)
fills corner \(c\) of target \(T\), the original sources fill
\(T\setminus\{c\}\), so \(c\in E_T\subset E\). This
contradicts the choice of \(R\) avoiding \(B\).

Therefore \(B\) contains two adjacent edges, say \(uv,vw\).

## 3. One of the adjacent sources completes the assembly

An adjacent cut avoiding both directions of \(uv\) and \(vw\)
must put \(u,v,w\) on the same side. Since its side sizes are two
and three, the other two colours lie on the other side. Exactly two
tricolour classes have this property, and they are reverses of one
another.

The two given adjacent classes cannot both be among that reverse
pair. At least one therefore meets \(E\) and completes an opposite
target, as required.

## Consequences

* Eight capped opposite sources together with **any five adjacent
  sources of class multiplicity at most two** assemble: the five
  sources occupy at least three classes, so two are neither equal
  nor reverses.
* In the remaining fourteen-source regime with all class multiplicities
  at most two, **opposite total eight is settled**. Its six adjacent
  sources certainly contain the required pair.

The unresolved opposite totals in that regime are consequently
\(5,6,7\), before any further seven-source reductions.
