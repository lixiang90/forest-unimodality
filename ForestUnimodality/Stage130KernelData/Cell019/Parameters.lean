import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 42
  A := (19144960955156233641361041/200000000000000000000000000)
  B := (22637348892610601597263909/1000000000000000000000000000)
  C := (-77234411801693297894289003/1000000000000000000000000000)
  dδ := (4605709501954362294906531/200000000000000000000000000)
  dM := (3689719676883659090632639/20000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(38138277377125839873173163/50000000000000000000000000), (14856494813881839789360129/10000000000000000000000000), (11723466364749843826587039/10000000000000000000000000), (13539416062411588015379493/1000000000000000000000000)]
  retention := ![(4/5), (7/10), (1/100), (1/1000)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (101/255)
  hi := (103/255)
  vmin := (15554/65025)
  damping := (15554/65025)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell019
