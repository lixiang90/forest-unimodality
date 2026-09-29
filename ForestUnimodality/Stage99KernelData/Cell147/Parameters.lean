import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 5) where
  terms := Finset.univ
  scale := 116
  A := (5304753151012832596222779/25000000000000000000000000)
  B := (84676849383680238836369369/1000000000000000000000000000)
  C := (64256334727101360737577807/100000000000000000000000000)
  dδ := (3493151664082334850736089/25000000000000000000000000)
  dM := (227301064038951121284559/156250000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(14320549124138015173457461/2000000000000000000000000), (6204028098163452131785789/2500000000000000000000000), (2595556867660272493125717/2500000000000000000000000), (22823841108697461521614969/1000000000000000000000000), (1020908292812118745018779/50000000000000000000000)]
  retention := ![(4/5), (7/10), (3/5), (3/20), (1/10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (47887/90312)
  hi := (31933/60208)
  vmin := (902905575/3625003264)
  damping := (902905575/3625003264)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell147
