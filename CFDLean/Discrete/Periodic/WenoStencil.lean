/-! Uniform and graded finite-volume WENO-JS5, in coordinates scaled by the owning cell width. -/
namespace CFDLean.GradedWeno

structure Stencil (K : Type) where
  farLeft : K
  left : K
  center : K
  right : K
  farRight : K

def gather {I K : Type} (prev next : I → I) (f : I → K) (i : I) : Stencil K :=
  ⟨f (prev (prev i)), f (prev i), f i, f (next i), f (next (next i))⟩

variable {K : Type} [Add K] [Sub K] [Mul K] [Div K] [∀ n, OfNat K n]

/-- Value and smoothness of the quadratic fitting three cell averages. The middle cell has
width m and its center is at -z relative to the unit-width owning cell's center. -/
def candidate (l m r z ul um ur : K) : K × K :=
  let backward := 2*(um-ul)/(l+m)
  let forward := 2*(ur-um)/(m+r)
  let a := 3*(forward-backward)/(2*(l+m+r))
  let b := backward + a*(2*l+m)/3
  let y := z + 1/2
  let gradient := b + 2*a*z
  (um + b*y + a*(y*y - m*m/12), gradient*gradient + 13/3*a*a)

/-- The two Neville blends of primitive interpolants give these positive ideal weights at the shared
endpoint. All three are scaled by ten so equal widths give (1,6,3). -/
def ideal (l₂ l₁ r₁ r₂ : K) : K × K × K :=
  let left := l₂ + l₁ + 1
  let right := r₁ + r₂
  let p := 10*right/(left+right)
  let q := 10*left/(left+right)
  (p*r₁/(left+r₁), p*left/(left+r₁) + q*right/(l₁+1+right), q*(l₁+1)/(l₁+1+right))

/-- Combine the three quadratic traces using the Jiang–Shu squared inverse smoothness weights. -/
def blend (ε : K) (d : K × K × K) (l c r : K × K) : K :=
  let weight (k β : K) := k / ((ε+β)*(ε+β))
  let a := weight d.1 l.2
  let b := weight d.2.1 c.2
  let e := weight d.2.2 r.2
  (a*l.1 + b*c.1 + e*r.1)/(a+b+e)

/-- Right endpoint of the center cell. Reverse widths and averages together for its left endpoint. -/
def edge (ε : K) (w u : Stencil K) : K :=
  let a := w.farLeft/w.center
  let b := w.left/w.center
  let d := w.right/w.center
  let e := w.farRight/w.center
  blend ε (ideal a b d e)
    (candidate a b 1 ((b+1)/2) u.farLeft u.left u.center)
    (candidate b 1 d 0 u.left u.center u.right)
    (candidate 1 d e ((0-(1+d))/2) u.center u.right u.farRight)

end CFDLean.GradedWeno
