import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell225
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 22
  A := (4537367959469909277414601/6250000000000000000000000)
  B := (3727634019257923536638799/200000000000000000000000000)
  C := (12920663618033864650236353/100000000000000000000000000)
  dδ := (58758039390881082464357377/1000000000000000000000000000)
  dM := (43346835742537922868400369/100000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(19240530249709977272942751/10000000000000000000000000), (6767609986989142178970269/1000000000000000000000000)]
  retention := ![(4/5), (1/5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (467/742)
  hi := (236/371)
  vmin := (31860/137641)
  damping := (31860/137641)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell225
