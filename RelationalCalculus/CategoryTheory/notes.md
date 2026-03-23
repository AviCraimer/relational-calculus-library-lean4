<!-- https://www.overleaf.com/project/67d73dc391f22eebf1637226 -->

## Definition Relator

Let $\mathcal{C}$ and $\mathcal{D}$ be categories. A relator $R$ from $\mathcal{C}$ to $\mathcal{D}$ consists of:

A relation $R_{ob} \subseteq Ob(\mathcal{C}) \times Ob(\mathcal{D})$

A relation $R_m \subseteq Morphism(\mathcal{C}) \times Morphisms(\mathcal{D})$

Note: $R_{ob}$ and $R_m$ are just regular relations between sets satisfying the following conditions:

1. Identities for related objects:

For all objects $c \in Ob(\mathcal{C})$ and $d \in Ob(\mathcal{D})$,

$(c, d) \in R_{ob}$ if and only if, $(id_c, id_d) \in R_m$.


2. Objects Endpoints for Related Morphisms:

For all objects $c, c' \in Ob(\mathcal{C})$ and $c, c' \in Ob(\mathcal{D})$, and for all morphisms $f \in \mathcal{C}[c, c'], g \in \mathcal{D}[c, d']$

if $(f, g) \in R_m$, then

$(c, d) \in R_{ob}$ and $(c', d') \in R_{ob}$

This ensures that for any related morphisms, the object endpoints of those morphisms are also related.


3. Composition for related composable pairs of morphims:

For any $f₁: c₁ \to c₂$ and $f₂: c₂ \to c₃$ in $\mathcal{C}$ and corresponding $g₁: d₁ \to d₂$ and $g₂: d₂ \to d₃$ in $\mathcal{D}$

If $(f₁, g₁) \in R_m$ and $(f₂, g₂) \in R_m$, then

$(f₁;f₂, g₁;g₂) \in R_m$.


# Composition of Relators


$$R;S_{ob} := R_{ob};S_{ob}$$

For morphisms you do a preliminary composition:

$$RS_{pre} := R_m;S_m$$

$$((f: c \to c'),(h: e \to e')) \in  (R;S)_m   :=$$
$$\text{either}$$
$$1. (f,h) \in RS_{pre}$$
$$\text{or}$$
     $$2. \text{There exists} (f_1, f_2) (h_1, h_2) \text{ such that}$$
     $$f = f_1;f_2 \text{ and}$$
     $$h = h_1;h_2  \text{ and}$$
     $$(f1, h1) \in RS_{pre}  \text{ and}$$
     $$( f2, h2) \in  RS_{pre}$$

The second disjunct ensures that compositions of morphisms with be related when their components are related. Note that crucially composable morphisms may be sent to non-composable morphisms in the middle category and then rejoined.

# Defining Natural Transformation between relators

For relators,
$$ R, S: C \to D$$

Definiton of a natural transformation $\alpha :R \to S$

The set of component indexes for transformations $R \to S$ is triple $(c, d, d')$ such that $(c,d) \in R_{m}$ and $(c,d') \in S_m$.

$$CompIndex: R \to S := \{(c, d, d') : C \times D \times D | \; (c,d) \in R_{m} \wedge (c,d') \in S_m  \} $$

We then define a natural transformation $\alpha$ as the minimal relator $\alpha : C \to D$ which is such that,

For every index $(c_1,d_1,d_1') \in CompIndex: R \to S$

$$1. (c_1,d_1), (c_1, d_1') \in  \alpha_{ob}$$

$$2. (Id_{c_1}, \alpha_{(c_1, d_1, d_1')}: d_1 \to d_1') \in \alpha_m \text{ For some morphism } \alpha_{(c_1, d_1, d_1')} \text{ in } D$$


3. The naturality commuting squares.

For every triple  $(f, g, g')$ such that $(f,g) \in R_m$ and $(f,g') \in S_m$ there is a commuting square in D.

$$\alpha_{(c1,d1,d1')};g' = g;\alpha_{(c2,d2,d2')}$$

## Comment
It is a surprise that a natural transformation is not only a relator, but a relator with the same domain/codomain as the relators it is transforming.\

Further, it seems likely that vertical composition of natural transformations may be the relator union operation. This is because relator union must add in the compositions, for for any two relators with matching types, we can perform vertical composition. I'm not sure if this "union" will be well behaved as a join however, so it might make more sense just to call it vertical composition of relators.

The next obvious thing to think about is whether ordinary relator composition can be used to define horizontal composition of natural transformations. If so, it is really a beautiful theory.

According to Claude:
   - The key for horizontal composition will be verifying the interchange law: (α' ∘ α);(β' ∘ β) = (α';β') ∘ (α;β)
   - -- I think ∘ is vertical and ; is horizontal
   - Bicategorical structure: This framework appears to define a bicategory (or possibly even a double category), which is a significant achievement.

There is some kind of analogy between the way that relations between sets can be viewed as sets, and the fact that natural transformations between relators can be viewed as relators.





