import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 36
  A := (16655094040919913628329141/5000000000000000000000000)
  B := (-77613507948897209054450741/1000000000000000000000000000)
  C := (-40516415549178910748828741/10000000000000000000000000000)
  dδ := (14248809720638311304696799/100000000000000000000000000)
  dM := 0
  wL := 0
  wR := 0
  wC := 1
  price := ![(38550046821477836900271541/5000000000000000000000000), (16009829001691142646990329/2500000000000000000000000), (5015730277512252399674253/200000000000000000000000)]
  retention := ![(4/5), (1/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (47/97)
  hi := (9237/19012)
  vmin := (2350/9409)
  damping := (2350/9409)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell047
