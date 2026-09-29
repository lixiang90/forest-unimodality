import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 60
  A := (-67105934694507656356421421/100000000000000000000000000)
  B := (16464450557903831384720661/200000000000000000000000000)
  C := (50301517430342418402133831/10000000000000000000000000000)
  dδ := (1236570729539148479764199/15625000000000000000000000)
  dM := (5991222072474546586975941/5000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(14522576299068630234501143/10000000000000000000000000), (67013465411080375133678899/10000000000000000000000000), (5799199467648720407453311/125000000000000000000000), (47076403659028258630314667/10000000000000000000000000)]
  retention := ![(4/5), (7/10), (1/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (4657/8862)
  hi := (111/211)
  vmin := (11100/44521)
  damping := (11100/44521)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell123
