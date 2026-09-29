import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell088.Parameters
import ForestUnimodality.BinomialMassData.Q405_808.Batch000_049
import ForestUnimodality.BinomialMassData.Q405_808.Batch050_099
import ForestUnimodality.BinomialMassData.Q203_404.Batch000_049
import ForestUnimodality.BinomialMassData.Q203_404.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree000.table
  base := (199413172735656661577152703/5000000000000000000000000)
  polynomial :=
    { denominator := 250000000000000000000000000000000000000
      center := (2)
      previous := (1)
      next := (1)
      square := (29434613003257531493872535000000000000)
      linear := (-90749786091301449077531350000000000)
      constant := (9970658636782833078857635150000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree000.table
  base := (199413172735656661577152703/5000000000000000000000000)
  polynomial :=
    { denominator := 250000000000000000000000000000000000000
      center := (2)
      previous := (1)
      next := (1)
      square := (29434613003257531493872535000000000000)
      linear := (-90749786091301449077531350000000000)
      constant := (9970658636782833078857635150000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 0 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 0 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree001.table
  base := (11686479584127951919662191201059182463729/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5100500000000000000000000000000000000000000
      center := (40804)
      previous := (20402)
      next := (20402)
      square := (600524974492460157537987459070000000000000)
      linear := (-603862899584959395042507816690200000000000)
      constant := (119365581655122357347770217876765626562499529) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree001.table
  base := (116662589373542235598567165633982913746201/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (408040)
      previous := (204020)
      next := (204020)
      square := (6005249744924601575379874590700000000000000)
      linear := (-6053493475416239003829483797077000000000000)
      constant := (1191600591122889544628199581377123703124996401) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 1 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 1 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (12499846827803811301/25000000000000000000)
  directionHi := (9999877462243049041/20000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree002.table
  base := (141383023279527388366250714448262475798941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-24117486440681681158418716775554000000000000)
      constant := (1454355372669107827090074808668880515624997141) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree002.table
  base := (1761670553950532310538567660825316853893/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2550250000000000000000000000000000000000000
      center := (20402)
      previous := (10201)
      next := (10201)
      square := (300262487246230078768993729535000000000000)
      linear := (-604423608973706534300908482406350000000000)
      constant := (36245775704943685080245824052496389453124986) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 2 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 2 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12499846827803811301/25000000000000000000)
  centralHi := (9999877462243049041/20000000000000000000)
  directionLo := (35354905822932919159/50000000000000000000)
  directionHi := (70709811645865838319/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree003.table
  base := (88645761333187244195303605769539671777539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-36157714889664174415987277217304000000000000)
      constant := (931488662897802704216373568115884816802675339) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree003.table
  base := (5516547968109354720856098457342623615501/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12751250000000000000000000000000000000000000
      center := (102010)
      previous := (51005)
      next := (51005)
      square := (1501312436231150393844968647675000000000000)
      linear := (-4530862720883005592051713874794250000000000)
      constant := (115967069901502028759063676713130332003451402) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 3 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 3 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35354905822932919159/50000000000000000000)
  centralHi := (70709811645865838319/100000000000000000000)
  directionLo := (86601479170339441739/100000000000000000000)
  directionHi := (4330073958516972087/5000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree004.table
  base := (28837324593905757557668630065845287311963/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (408040)
      previous := (204020)
      next := (204020)
      square := (6005249744924601575379874590700000000000000)
      linear := (-24098971669323333836777918829527000000000000)
      constant := (318346731371729862719935072267280275869334563) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree004.table
  base := (28690473182058038019911831090257845890571/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (408040)
      previous := (204020)
      next := (204020)
      square := (6005249744924601575379874590700000000000000)
      linear := (-24158429587589914050395541350227000000000000)
      constant := (316968149132483437219949187353401285929714771) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 4 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 4 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86601479170339441739/100000000000000000000)
  centralHi := (4330073958516972087/5000000000000000000)
  directionLo := (99998774622430490409/100000000000000000000)
  directionHi := (9999877462243049041/10000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree005.table
  base := (4853323205716113318001327400849652833327/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12751250000000000000000000000000000000000000
      center := (102010)
      previous := (51005)
      next := (51005)
      square := (1501312436231150393844968647675000000000000)
      linear := (-7529771473453645116390549762600500000000000)
      constant := (58950062111079251840762925240227074177768727) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree005.table
  base := (38608157150184615488490593531767999113633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-60386816583295611465168454402554000000000000)
      constant := (469745528685447236236801456806955358958170233) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 5 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 5 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99998774622430490409/100000000000000000000)
  centralHi := (9999877462243049041/10000000000000000000)
  directionLo := (111802028861217721361/100000000000000000000)
  directionHi := (55901014430608860681/50000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree006.table
  base := (838976499349179684941175306089039553161/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 12751250000000000000000000000000000000000000
      center := (102010)
      previous := (51005)
      next := (51005)
      square := (1501312436231150393844968647675000000000000)
      linear := (-9034800029576456773586619817819250000000000)
      constant := (47826302398423498382726023445543419927181444) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree006.table
  base := (26685859336662253392346286394416912619927/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-72456773991411394829545826104654000000000000)
      constant := (381501476717757009451740061558939925635875327) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 6 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 6 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111802028861217721361/100000000000000000000)
  centralHi := (55901014430608860681/50000000000000000000)
  directionLo := (30618246591066282437/25000000000000000000)
  directionHi := (122472986364265129749/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree007.table
  base := (18856844059038011221347290250551261486959/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-84318628685594147446261518984304000000000000)
      constant := (340346470130690587446596585738494043428468759) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree007.table
  base := (4684092868606831534442861444514781227843/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (204020)
      previous := (102010)
      next := (102010)
      square := (3002624872462300787689937295350000000000000)
      linear := (-21131682849881794548480799451688500000000000)
      constant := (84962228474851525890545940191413033305226443) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 7 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 7 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30618246591066282437/25000000000000000000)
  centralHi := (122472986364265129749/100000000000000000000)
  directionLo := (66142972265536994977/50000000000000000000)
  directionHi := (26457188906214797991/20000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree008.table
  base := (3314167746755625798846081772477174987477/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (204020)
      previous := (102010)
      next := (102010)
      square := (3002624872462300787689937295350000000000000)
      linear := (-24089714283644160175957519856513500000000000)
      constant := (82125070363247951664598469893507162047252877) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree008.table
  base := (13164983763820959317633504492967735656257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-96596688807642961558300569508854000000000000)
      constant := (328520205564074340740973236524687871429477657) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 8 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 8 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66142972265536994977/50000000000000000000)
  centralHi := (26457188906214797991/20000000000000000000)
  directionLo := (141419623291731676637/100000000000000000000)
  directionHi := (70709811645865838319/50000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree009.table
  base := (9144696338540946269085252349702524383407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-108399085583559133961398639867804000000000000)
      constant := (337870220391087006791965552378153576235134807) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree009.table
  base := (9073311248801851222925166630591828471273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-108666646215758744922677941210954000000000000)
      constant := (338350926775184402254525063272919242235455873) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 9 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 9 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141419623291731676637/100000000000000000000)
  centralHi := (70709811645865838319/50000000000000000000)
  directionLo := (74999080966822867807/50000000000000000000)
  directionHi := (29999632386729147123/20000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree010.table
  base := (48008016599766830691975116664266272441/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20402000000000000000000000000000000000000000
      center := (163216)
      previous := (81608)
      next := (81608)
      square := (2402099897969840630151949836280000000000000)
      linear := (-24087862806508325443793440061910800000000000)
      constant := (72630520606597640395996650243209506129266025) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree010.table
  base := (2972094372217470678914969630610146103993/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (408040)
      previous := (204020)
      next := (204020)
      square := (6005249744924601575379874590700000000000000)
      linear := (-60368301811937264143527656456527000000000000)
      constant := (182032737740606867992507598317181600406832593) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 10 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 10 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74999080966822867807/50000000000000000000)
  centralHi := (29999632386729147123/20000000000000000000)
  directionLo := (79055972758181150399/50000000000000000000)
  directionHi := (158111945516362300799/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree011.table
  base := (1758825230124659267992582940461286815733/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (408040)
      previous := (204020)
      next := (204020)
      square := (6005249744924601575379874590700000000000000)
      linear := (-66239771240762060238267880375652000000000000)
      constant := (200603078266558837113208899171610899307292333) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree011.table
  base := (5554530097791942519754494498549850633/16000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20402000000000000000000000000000000000000000
      center := (163216)
      previous := (81608)
      next := (81608)
      square := (2402099897969840630151949836280000000000000)
      linear := (-26561312206398062330286536923030800000000000)
      constant := (80508397852660006412456649889689978288404125) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 11 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 11 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79055972758181150399/50000000000000000000)
  centralHi := (158111945516362300799/100000000000000000000)
  directionLo := (82914603729478850989/50000000000000000000)
  directionHi := (165829207458957701979/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree012.table
  base := (1506148525027396988386050784606069375933/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-144519770930506613734104321193054000000000000)
      constant := (450108064111146852120416919049821513703892533) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree012.table
  base := (367062518652679534831549172776616756511/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (204020)
      previous := (102010)
      next := (102010)
      square := (3002624872462300787689937295350000000000000)
      linear := (-36219129610026523753952514079313500000000000)
      constant := (112967611091314447922919128402915767533168711) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 12 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 12 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82914603729478850989/50000000000000000000)
  centralHi := (165829207458957701979/100000000000000000000)
  directionLo := (86601479170339441739/50000000000000000000)
  directionHi := (173202958340678883479/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree013.table
  base := (-1532818879487453441707605893473379313/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5100500000000000000000000000000000000000000
      center := (40804)
      previous := (20402)
      next := (20402)
      square := (600524974492460157537987459070000000000000)
      linear := (-7827999968974455349583644081740200000000000)
      constant := (25431823439246468477058281660998296538140435) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree013.table
  base := (-184777181420117651969321146179981762633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-156946475848221878380187428019354000000000000)
      constant := (510837205208332011278962383332132006039380767) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 13 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 13 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86601479170339441739/50000000000000000000)
  centralHi := (173202958340678883479/100000000000000000000)
  directionLo := (90137677346185064761/50000000000000000000)
  directionHi := (180275354692370129523/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree014.table
  base := (-76991204027823496675193876876168291459/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5100500000000000000000000000000000000000000
      center := (40804)
      previous := (20402)
      next := (20402)
      square := (600524974492460157537987459070000000000000)
      linear := (-8430011391423580012462072103827700000000000)
      constant := (28799181084600713105732115370959207258826741) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree014.table
  base := (-62646815637747382551708450002212746309/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20402000000000000000000000000000000000000000
      center := (163216)
      previous := (81608)
      next := (81608)
      square := (2402099897969840630151949836280000000000000)
      linear := (-33803286651267532348912959944290800000000000)
      constant := (115727951959216615756479678907040538874509455) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 14 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 14 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90137677346185064761/50000000000000000000)
  centralHi := (180275354692370129523/100000000000000000000)
  directionLo := (3741611537343595959/2000000000000000000)
  directionHi := (187080576867179797951/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree015.table
  base := (-2707891025691093170061978485263099051657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-180640456277454093506810002518304000000000000)
      constant := (651594456095896407341879973030571751574046943) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree015.table
  base := (-1365006772021218013538939781844086254479/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (408040)
      previous := (204020)
      next := (204020)
      square := (6005249744924601575379874590700000000000000)
      linear := (-90543195332226722554471085711777000000000000)
      constant := (327363198672839943376513886347305976118059721) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 15 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 15 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3741611537343595959/2000000000000000000)
  centralHi := (187080576867179797951/100000000000000000000)
  directionLo := (48411698594227770219/25000000000000000000)
  directionHi := (193646794376911080877/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree016.table
  base := (-3696212049131137068219261972010383576493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-192680684726436586764378562960054000000000000)
      constant := (735073894144309102154247430753262077136194907) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree016.table
  base := (-3714820701327164600077206302710265053649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-193156348072569228473319543125654000000000000)
      constant := (738704235924831740304117987230700586187726551) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 16 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 16 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48411698594227770219/25000000000000000000)
  centralHi := (193646794376911080877/100000000000000000000)
  directionLo := (199997549244860980819/100000000000000000000)
  directionHi := (9999877462243049041/5000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree017.table
  base := (-4533187536724437048832461924751415183647/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-204720913175419080021947123401804000000000000)
      constant := (826132223501218577423585137798068938711616953) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree017.table
  base := (-909769280036638605057478966949389662407/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20402000000000000000000000000000000000000000
      center := (163216)
      previous := (81608)
      next := (81608)
      square := (2402099897969840630151949836280000000000000)
      linear := (-41045261096137002367539382965550800000000000)
      constant := (166057010199534192427892033418064476053786193) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 17 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 17 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199997549244860980819/100000000000000000000)
  centralHi := (9999877462243049041/5000000000000000000)
  directionLo := (206152755100307852147/100000000000000000000)
  directionHi := (51538188775076963037/25000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree018.table
  base := (-5240146066905588932122632832882165313801/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-216761141624401573279515683843554000000000000)
      constant := (924551871338013521187818117318664031633915999) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree018.table
  base := (-5253315812228548780418382803946464517149/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-217296262888800795202074286529854000000000000)
      constant := (929252324588522053958935238365521115460563051) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 18 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 18 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (206152755100307852147/100000000000000000000)
  centralHi := (51538188775076963037/25000000000000000000)
  directionLo := (53032358734399378739/25000000000000000000)
  directionHi := (212129434937597514957/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree019.table
  base := (-291669963666017533949220614965282171673/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5100500000000000000000000000000000000000000
      center := (40804)
      previous := (20402)
      next := (20402)
      square := (600524974492460157537987459070000000000000)
      linear := (-11440068503669203326854212214265200000000000)
      constant := (51508322133993677824393008556391687816763727) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree019.table
  base := (-5844463522342598141246473006936497753843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-229366220296916578566451658231954000000000000)
      constant := (1035440447697030600383349136227897786413047557) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 19 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 19 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53032358734399378739/25000000000000000000)
  centralHi := (212129434937597514957/100000000000000000000)
  directionLo := (43588455305707418143/20000000000000000000)
  directionHi := (54485569132134272679/25000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree020.table
  base := (-1581397492072078177008469241926304216961/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (204020)
      previous := (102010)
      next := (102010)
      square := (3002624872462300787689937295350000000000000)
      linear := (-60210399630591639948663201181763500000000000)
      constant := (285711742049581635365852175345841020682780839) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree020.table
  base := (-6334872195391265527263728404161195890549/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-241436177705032361930829029934054000000000000)
      constant := (1148721064558899306409463326417961640720509651) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 20 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 20 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43588455305707418143/20000000000000000000)
  centralHi := (54485569132134272679/25000000000000000000)
  directionLo := (223604057722435442723/100000000000000000000)
  directionHi := (55901014430608860681/25000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree021.table
  base := (-1345322341760896798627269156757771904237/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20402000000000000000000000000000000000000000
      center := (163216)
      previous := (81608)
      next := (81608)
      square := (2402099897969840630151949836280000000000000)
      linear := (-50576365394269810610444273033760800000000000)
      constant := (252498504743693277914412717904017593804878363) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree021.table
  base := (-841798326756079166181129687202248547967/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12751250000000000000000000000000000000000000
      center := (102010)
      previous := (51005)
      next := (51005)
      square := (1501312436231150393844968647675000000000000)
      linear := (-31688266889143518161900800204519250000000000)
      constant := (158624218568258732195862770915854612562188633) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 21 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 21 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223604057722435442723/100000000000000000000)
  centralHi := (55901014430608860681/25000000000000000000)
  directionLo := (114562988527529205487/50000000000000000000)
  directionHi := (9165039082202336439/4000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree022.table
  base := (-3522129483883160292494046605193396649789/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (408040)
      previous := (204020)
      next := (204020)
      square := (6005249744924601575379874590700000000000000)
      linear := (-132461027710165773154894962805277000000000000)
      constant := (694511798911133075820336069871337160775502411) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree022.table
  base := (-1762690150086821642458339136880581428947/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (204020)
      previous := (102010)
      next := (102010)
      square := (3002624872462300787689937295350000000000000)
      linear := (-66394023130315982164895943334563500000000000)
      constant := (349044850729996963511481968536016438843311653) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 22 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 22 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114562988527529205487/50000000000000000000)
  centralHi := (9165039082202336439/4000000000000000000)
  directionLo := (234517914226039596771/100000000000000000000)
  directionHi := (58629478556509899193/25000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree023.table
  base := (-7284701245030219547363779977925984875751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-276962283869314039567358486052304000000000000)
      constant := (1522377255441690721221669037940037653282464049) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree023.table
  base := (-1458025834803259507715109322684244233279/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20402000000000000000000000000000000000000000
      center := (163216)
      previous := (81608)
      next := (81608)
      square := (2402099897969840630151949836280000000000000)
      linear := (-55529209985875942404792229008070800000000000)
      constant := (306043088868879405882925981040241824576320921) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 23 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 23 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234517914226039596771/100000000000000000000)
  centralHi := (58629478556509899193/25000000000000000000)
  directionLo := (239788637813448069871/100000000000000000000)
  directionHi := (14986789863340504367/6250000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree024.table
  base := (-931604692645791578723356828965179366563/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12751250000000000000000000000000000000000000
      center := (102010)
      previous := (51005)
      next := (51005)
      square := (1501312436231150393844968647675000000000000)
      linear := (-36125314039787066603115880811756750000000000)
      constant := (207812940233990497539770698187677455281690837) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree024.table
  base := (-3728680900345747300596191182845269078769/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (408040)
      previous := (204020)
      next := (204020)
      square := (6005249744924601575379874590700000000000000)
      linear := (-144858003668747747694169258371227000000000000)
      constant := (835526099700173149258185821042881410127477431) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 24 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 24 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239788637813448069871/100000000000000000000)
  centralHi := (14986789863340504367/6250000000000000000)
  directionLo := (244945972728530259497/100000000000000000000)
  directionHi := (122472986364265129749/50000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree025.table
  base := (-472035408388021368607252127104961597297/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12751250000000000000000000000000000000000000
      center := (102010)
      previous := (51005)
      next := (51005)
      square := (1501312436231150393844968647675000000000000)
      linear := (-37630342595909878260311950866975500000000000)
      constant := (226170328337293042272552176464814339116946606) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree025.table
  base := (-7556331747177372284707685281318701327703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-301785964745611278752715888444554000000000000)
      constant := (1818650156893163012680983081910967927756101697) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 25 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 25 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244945972728530259497/100000000000000000000)
  centralHi := (122472986364265129749/50000000000000000000)
  directionLo := (31249617069509528253/12500000000000000000)
  directionHi := (9999877462243049041/4000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree026.table
  base := (-3793497733083516492352004034211336813411/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (408040)
      previous := (204020)
      next := (204020)
      square := (6005249744924601575379874590700000000000000)
      linear := (-156541484608130759670032083688777000000000000)
      constant := (981461436472599885280276763539142653166394389) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree026.table
  base := (-7590124371609861065984623129060501509737/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-313855922153727062117093260146654000000000000)
      constant := (1972977843084502545113983050267756824099172863) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 26 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 26 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31249617069509528253/12500000000000000000)
  centralHi := (9999877462243049041/4000000000000000000)
  directionLo := (254947851567570017351/100000000000000000000)
  directionHi := (31868481445946252169/12500000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree027.table
  base := (-1511720662575088729045395684397859871953/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20402000000000000000000000000000000000000000
      center := (163216)
      previous := (81608)
      next := (81608)
      square := (2402099897969840630151949836280000000000000)
      linear := (-65024639533048802519526545563860800000000000)
      constant := (424631794516003491865032439636291556446207447) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree027.table
  base := (-7561199825496313387953726639442814222739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-325925879561842845481470631848754000000000000)
      constant := (2134010161968838393545037203174024852113839461) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 27 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 27 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254947851567570017351/100000000000000000000)
  centralHi := (31868481445946252169/12500000000000000000)
  directionLo := (259804437511018325217/100000000000000000000)
  directionHi := (129902218755509162609/50000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree028.table
  base := (-3734684585838942843982222497539365878857/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (408040)
      previous := (204020)
      next := (204020)
      square := (6005249744924601575379874590700000000000000)
      linear := (-168581713057113252927600644130527000000000000)
      constant := (1145025368415394039856951923270498428669779743) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree028.table
  base := (-7471521051398941501819087886270864414193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-337995836969958628845848003550854000000000000)
      constant := (2301727089569093430799612597384884912110817207) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 28 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 28 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259804437511018325217/100000000000000000000)
  centralHi := (129902218755509162609/50000000000000000000)
  directionLo := (264571889062147979909/100000000000000000000)
  directionHi := (26457188906214797991/10000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree029.table
  base := (-1830218448298345718490232059198892372213/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (204020)
      previous := (102010)
      next := (102010)
      square := (3002624872462300787689937295350000000000000)
      linear := (-87300913640802249778192462175701000000000000)
      constant := (615895510115111742585090829763896630161055187) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree029.table
  base := (-3661327488276508820493302439756082606731/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (408040)
      previous := (204020)
      next := (204020)
      square := (6005249744924601575379874590700000000000000)
      linear := (-175032897189037206105112687626477000000000000)
      constant := (1238056320830270322412367833650329201328737069) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 29 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 29 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264571889062147979909/100000000000000000000)
  centralHi := (26457188906214797991/10000000000000000000)
  directionLo := (16828433807915238377/6250000000000000000)
  directionHi := (269254940926643814033/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree030.table
  base := (-7114380154982606642169682970948428877629/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-361243883012191492370338409144554000000000000)
      constant := (2643739999834897721855778463267555077019306571) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree030.table
  base := (-7115852787261946519776605898585706711183/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-362135751786190195574602746955054000000000000)
      constant := (2657154054891699004129624744142992205839222217) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 30 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 30 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16828433807915238377/6250000000000000000)
  centralHi := (269254940926643814033/100000000000000000000)
  directionLo := (273857922917901650441/100000000000000000000)
  directionHi := (136928961458950825221/50000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree031.table
  base := (-6850897555901388240275015536707288559111/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-373284111461173985627906969586304000000000000)
      constant := (2830514319096511999702521670211029574408508689) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree031.table
  base := (-6852113756312114035100431758222592807863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-374205709194305978938980118657154000000000000)
      constant := (2844841135680874586179887240260814330766989537) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 31 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 31 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273857922917901650441/100000000000000000000)
  centralHi := (136928961458950825221/50000000000000000000)
  directionLo := (278384806834719832723/100000000000000000000)
  directionHi := (69596201708679958181/25000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree032.table
  base := (-6531232684477670170918696159537377465619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-385324339910156478885475530028054000000000000)
      constant := (3023896769215616262411144241816039212473220581) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree032.table
  base := (-1306447214639419798624825665537832081591/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20402000000000000000000000000000000000000000
      center := (163216)
      previous := (81608)
      next := (81608)
      square := (2402099897969840630151949836280000000000000)
      linear := (-77255133320484352460671498071850800000000000)
      constant := (607833148339408678714764664348347774935690209) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 32 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 32 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (278384806834719832723/100000000000000000000)
  centralHi := (69596201708679958181/25000000000000000000)
  directionLo := (141419623291731676637/50000000000000000000)
  directionHi := (11313569863338534131/4000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree033.table
  base := (-6156030353547109753684860755602021158507/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-397364568359138972143044090469804000000000000)
      constant := (3223880772456473969664568407601801907162070093) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree033.table
  base := (-3078428683539869627922221145937896201929/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (408040)
      previous := (204020)
      next := (204020)
      square := (6005249744924601575379874590700000000000000)
      linear := (-199172812005268772833867431030677000000000000)
      constant := (1620060684242557658640602087826599520844122271) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 33 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 33 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141419623291731676637/50000000000000000000)
  centralHi := (11313569863338534131/4000000000000000000)
  directionLo := (287224612697794577817/100000000000000000000)
  directionHi := (143612306348897288909/50000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree034.table
  base := (-5725806016532065326697507336591464914427/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-409404796808121465400612650911554000000000000)
      constant := (3430461070678723644055591263851065466407930173) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree034.table
  base := (-5726487035981201114401460764845341677221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-410415581418653329032112233763454000000000000)
      constant := (3447702819675876439966109773344639669550668579) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 34 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 34 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (287224612697794577817/100000000000000000000)
  centralHi := (143612306348897288909/50000000000000000000)
  directionLo := (145772011091717303553/50000000000000000000)
  directionHi := (291544022183434607107/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree035.table
  base := (-5240971736618267230479218778015693443757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-421445025257103958658181211353304000000000000)
      constant := (3643633460425807650380541942650752536180234843) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree035.table
  base := (-5241532051620042091381428675978173218177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-422485538826769112396489605465554000000000000)
      constant := (3661905943750825756340637830291451655001376423) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 35 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 35 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (145772011091717303553/50000000000000000000)
  centralHi := (291544022183434607107/100000000000000000000)
  directionLo := (73950091109811995603/25000000000000000000)
  directionHi := (295800364439247982413/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree036.table
  base := (-2350928467101450544555556244173174596443/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (408040)
      previous := (204020)
      next := (204020)
      square := (6005249744924601575379874590700000000000000)
      linear := (-216742626853043225957874885897527000000000000)
      constant := (1931697290640127149044084482658521945941684957) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree036.table
  base := (-4702317563400104631876580547250913493167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-434555496234884895760866977167654000000000000)
      constant := (3882727423860894669622402462134951431456203433) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 36 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 36 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73950091109811995603/25000000000000000000)
  centralHi := (295800364439247982413/100000000000000000000)
  directionLo := (74999080966822867807/25000000000000000000)
  directionHi := (299996323867291471229/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree037.table
  base := (-4108724966421324480257228544162881957123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-445525482155068945173318332236804000000000000)
      constant := (4089741746735925804528721459028752566155388277) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree037.table
  base := (-513637919179536618139154362935455995181/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12751250000000000000000000000000000000000000
      center := (102010)
      previous := (51005)
      next := (51005)
      square := (1501312436231150393844968647675000000000000)
      linear := (-55828181705375084890655543608719250000000000)
      constant := (513770576246091130246635749200431163393158619) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 37 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 37 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74999080966822867807/25000000000000000000)
  centralHi := (299996323867291471229/100000000000000000000)
  directionLo := (30413439967452834403/10000000000000000000)
  directionHi := (304134399674528344031/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree038.table
  base := (-3461786378122399480083168344429763625747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-457565710604051438430886892678554000000000000)
      constant := (4322672809024818927663234123915041981253754853) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree038.table
  base := (-138483879202704555543886993260004902543/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20402000000000000000000000000000000000000000
      center := (163216)
      previous := (81608)
      next := (81608)
      square := (2402099897969840630151949836280000000000000)
      linear := (-91739082210223292497924344114370800000000000)
      constant := (868843076954342532887854386285651249945794285) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 38 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 38 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30413439967452834403/10000000000000000000)
  centralHi := (304134399674528344031/100000000000000000000)
  directionLo := (308216923281124618007/100000000000000000000)
  directionHi := (38527115410140577251/12500000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree039.table
  base := (-1380604746833623511979065985674191390223/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (408040)
      previous := (204020)
      next := (204020)
      square := (6005249744924601575379874590700000000000000)
      linear := (-234802969526516965844227726560152000000000000)
      constant := (2281093025535062936415002874968687886128335177) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree039.table
  base := (-2761464277357804696205333454078848439127/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-470765368459232245853999092273954000000000000)
      constant := (4584878056596561353498181680823908667072465473) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 39 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 39 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (308216923281124618007/100000000000000000000)
  centralHi := (38527115410140577251/12500000000000000000)
  directionLo := (312246073679685475449/100000000000000000000)
  directionHi := (6244921473593709509/2000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree040.table
  base := (-1003564441898510677083667981333417707191/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (408040)
      previous := (204020)
      next := (204020)
      square := (6005249744924601575379874590700000000000000)
      linear := (-240823083751008212473012006781027000000000000)
      constant := (2404140050057858062801742421597092805968944609) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree040.table
  base := (-50183443576068560454706832385154722791/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2550250000000000000000000000000000000000000
      center := (20402)
      previous := (10201)
      next := (10201)
      square := (300262487246230078768993729535000000000000)
      linear := (-12070883146683700730459411599401350000000000)
      constant := (120803781845846785684005231337029536672809009) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 40 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 40 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (312246073679685475449/100000000000000000000)
  centralHi := (6244921473593709509/2000000000000000000)
  directionLo := (79055972758181150399/25000000000000000000)
  directionHi := (316223891032724601597/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree041.table
  base := (-1199652134202065475386033768019588736359/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-493686395950998918203592574003804000000000000)
      constant := (5060953858679962496992979143245750300300401841) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree041.table
  base := (-1199823239889238696946779857682115048447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-494905283275463812582753835678154000000000000)
      constant := (5086033956577558640461224236492132744390792153) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 41 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 41 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79055972758181150399/25000000000000000000)
  centralHi := (316223891032724601597/100000000000000000000)
  directionLo := (320152288749234767617/100000000000000000000)
  directionHi := (160076144374617383809/50000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree042.table
  base := (-67773051323287559709119786497982795723/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20402000000000000000000000000000000000000000
      center := (163216)
      previous := (81608)
      next := (81608)
      square := (2402099897969840630151949836280000000000000)
      linear := (-101145324879996282292232226889110800000000000)
      constant := (1064041289871433171429715541711735077500829677) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree042.table
  base := (-339005349759006479039498463626884795503/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-506975240683579595947131207380254000000000000)
      constant := (5346525242008051659033381888919693148201073897) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 42 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 42 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (320152288749234767617/100000000000000000000)
  centralHi := (160076144374617383809/50000000000000000000)
  directionLo := (324033064243250193093/100000000000000000000)
  directionHi := (162016532121625096547/50000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree043.table
  base := (71895373152313570898806330073581114663/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12751250000000000000000000000000000000000000
      center := (102010)
      previous := (51005)
      next := (51005)
      square := (1501312436231150393844968647675000000000000)
      linear := (-64720856606120488089841211860913000000000000)
      constant := (698254646336050082875462936625131929075677263) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree043.table
  base := (575048348662269708395438580794518152701/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-519045198091695379311508579082354000000000000)
      constant := (5613624440755177815215346123110713879675702901) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 43 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 43 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (324033064243250193093/100000000000000000000)
  centralHi := (162016532121625096547/50000000000000000000)
  directionLo := (163933954273029736873/50000000000000000000)
  directionHi := (327867908546059473747/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree044.table
  base := (385594404265265337500960051823940709491/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (204020)
      previous := (102010)
      next := (102010)
      square := (3002624872462300787689937295350000000000000)
      linear := (-132451770324486599494074563832263500000000000)
      constant := (1464611365470356801918384568977539769177517691) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree044.table
  base := (61691354481859966579433661096561699949/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20402000000000000000000000000000000000000000
      center := (163216)
      previous := (81608)
      next := (81608)
      square := (2402099897969840630151949836280000000000000)
      linear := (-106223031099962232535177190156890800000000000)
      constant := (1177466200406599451153503946288826529505898745) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 44 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 44 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (163933954273029736873/50000000000000000000)
  centralHi := (327867908546059473747/100000000000000000000)
  directionLo := (82914603729478850989/25000000000000000000)
  directionHi := (331658414917915403957/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree045.table
  base := (640683672292335051222757041027065736281/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (204020)
      previous := (102010)
      next := (102010)
      square := (3002624872462300787689937295350000000000000)
      linear := (-135461827436732222808466703942701000000000000)
      constant := (1534357718651232142439675232347111628825802481) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree045.table
  base := (2562658051631190733182994903689643225593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-543185112907926946040263322486554000000000000)
      constant := (6167644485782993808407049767384548050544274193) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 45 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 45 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82914603729478850989/25000000000000000000)
  centralHi := (331658414917915403957/100000000000000000000)
  directionLo := (83851521645913291021/25000000000000000000)
  directionHi := (67081217316730632817/20000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree046.table
  base := (3636199065722685127332766289409786477549/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-553887538195911384491435376212554000000000000)
      constant := (6422993050438398196553090602327209231857477349) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree046.table
  base := (1818068225669995273046976129641912617977/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (408040)
      previous := (204020)
      next := (204020)
      square := (6005249744924601575379874590700000000000000)
      linear := (-277627535158021364702320347094327000000000000)
      constant := (3227282270208361293661229892096033650615983377) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 46 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 46 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83851521645913291021/25000000000000000000)
  centralHi := (67081217316730632817/20000000000000000000)
  directionLo := (169556171849374119961/50000000000000000000)
  directionHi := (339112343698748239923/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree047.table
  base := (119068566437209174230519158151441355799/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2550250000000000000000000000000000000000000
      center := (20402)
      previous := (10201)
      next := (10201)
      square := (300262487246230078768993729535000000000000)
      linear := (-14148194166122346943725098416357600000000000)
      constant := (167878292571089325450421366155383368895505599) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree047.table
  base := (4762691524473541826995317376390961938581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-567325027724158512769018065890754000000000000)
      constant := (6748090885032313454039494917048855202735464781) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 47 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 47 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (169556171849374119961/50000000000000000000)
  centralHi := (339112343698748239923/100000000000000000000)
  directionLo := (342778529637366387909/100000000000000000000)
  directionHi := (34277852963736638791/10000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree048.table
  base := (1485585752213767022281381027663570597297/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (204020)
      previous := (102010)
      next := (102010)
      square := (3002624872462300787689937295350000000000000)
      linear := (-144491998773469092751643124274013500000000000)
      constant := (1753461650687690495722442672270501083663026697) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree048.table
  base := (5942301270812837911263163820954702456737/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-579394985132274296133395437592854000000000000)
      constant := (7048223295205532321572326492401102919761174137) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 48 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 48 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (342778529637366387909/100000000000000000000)
  centralHi := (34277852963736638791/10000000000000000000)
  directionLo := (346405916681357766957/100000000000000000000)
  directionHi := (173202958340678883479/50000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree049.table
  base := (57399857345425896284038134031569845379/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20402000000000000000000000000000000000000000
      center := (163216)
      previous := (81608)
      next := (81608)
      square := (2402099897969840630151949836280000000000000)
      linear := (-118001644708571772852828211507560800000000000)
      constant := (1463827513407047804362931201036788724817779475) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree049.table
  base := (1793737028424950376199086277174621308847/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (204020)
      previous := (102010)
      next := (102010)
      square := (3002624872462300787689937295350000000000000)
      linear := (-147866235635097519874443202323738500000000000)
      constant := (1838740397909222535860957178740676311971548247) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 49 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 49 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (346405916681357766957/100000000000000000000)
  centralHi := (173202958340678883479/50000000000000000000)
  directionLo := (349995711178506716433/100000000000000000000)
  directionHi := (174997855589253358217/50000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree050.table
  base := (423032289231539751798835602989740252497/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5100500000000000000000000000000000000000000
      center := (40804)
      previous := (20402)
      next := (20402)
      square := (600524974492460157537987459070000000000000)
      linear := (-30102422599592067876085480898977700000000000)
      constant := (381550222465210855211722201716917090315721897) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree050.table
  base := (2115154502704675641229053160410077722593/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (204020)
      previous := (102010)
      next := (102010)
      square := (3002624872462300787689937295350000000000000)
      linear := (-150883724987126465715537545249263500000000000)
      constant := (1917076407770181039372159172596411952848171193) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 50 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 50 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349995711178506716433/100000000000000000000)
  centralHi := (174997855589253358217/50000000000000000000)
  directionLo := (353549058229329191593/100000000000000000000)
  directionHi := (176774529114664595797/50000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree051.table
  base := (9799322386143370894935601341535959672127/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-614088680440823850779278178421304000000000000)
      constant := (7949447132531116574582760432182538949615367527) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree051.table
  base := (4899649871857111794844971910479349875279/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (408040)
      previous := (204020)
      next := (204020)
      square := (6005249744924601575379874590700000000000000)
      linear := (-307802428678310823113263776349577000000000000)
      constant := (3994127649548785834934766847669676348077721079) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 51 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 51 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (353549058229329191593/100000000000000000000)
  centralHi := (176774529114664595797/50000000000000000000)
  directionLo := (178533522977018601317/50000000000000000000)
  directionHi := (71413409190807440527/20000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree052.table
  base := (11191002802124638924280801636480899257143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-626128908889806344036846738863054000000000000)
      constant := (8274465523166735319515290641864146653322115743) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree052.table
  base := (11190984350120048453160415678758934110413/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-627674814764737429590904924401254000000000000)
      constant := (8314810504263353989785631118428325886860323013) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 52 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 52 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (178533522977018601317/50000000000000000000)
  centralHi := (71413409190807440527/20000000000000000000)
  directionLo := (72110141876948051809/20000000000000000000)
  directionHi := (180275354692370129523/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree053.table
  base := (12635679701932654095654969588644803803167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-638169137338788837294415299304804000000000000)
      constant := (8606059546431194857797761403808763768596106567) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree053.table
  base := (39486452094978386245278392130131129633/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 2550250000000000000000000000000000000000000
      center := (20402)
      previous := (10201)
      next := (10201)
      square := (300262487246230078768993729535000000000000)
      linear := (-15993619304321330323882057402583850000000000)
      constant := (216199279338563797996590474630729091227089864) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 53 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 53 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72110141876948051809/20000000000000000000)
  centralHi := (180275354692370129523/50000000000000000000)
  directionLo := (364001034022344968907/100000000000000000000)
  directionHi := (91000258505586242227/25000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree054.table
  base := (3533336806472141461041500083009435712997/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (204020)
      previous := (102010)
      next := (102010)
      square := (3002624872462300787689937295350000000000000)
      linear := (-162552341446942832637995964936638500000000000)
      constant := (2236057285637477808704427089069606753708282397) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree054.table
  base := (14133334985118102583552239235307597534531/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-651814729580968996319659667805454000000000000)
      constant := (8987737248591410735167393289286009802449750731) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 54 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 54 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (364001034022344968907/100000000000000000000)
  centralHi := (91000258505586242227/25000000000000000000)
  directionLo := (73483791818559077849/20000000000000000000)
  directionHi := (183709479546397694623/50000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree055.table
  base := (156840006902775054597026661333665039877/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5100500000000000000000000000000000000000000
      center := (40804)
      previous := (20402)
      next := (20402)
      square := (600524974492460157537987459070000000000000)
      linear := (-33112479711837691190477621009415200000000000)
      constant := (464448713187215453743164343258290616608926385) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree055.table
  base := (7841995362778774442184436592094725044581/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (408040)
      previous := (204020)
      next := (204020)
      square := (6005249744924601575379874590700000000000000)
      linear := (-331942343494542389842018519753777000000000000)
      constant := (4667054341402119310797911905644165790179770781) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 55 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 55 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73483791818559077849/20000000000000000000)
  centralHi := (183709479546397694623/50000000000000000000)
  directionLo := (370805380533144588443/100000000000000000000)
  directionHi := (92701345133286147111/25000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree056.table
  base := (4321909087875453170156261580011862828959/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (204020)
      previous := (102010)
      next := (102010)
      square := (3002624872462300787689937295350000000000000)
      linear := (-168572455671434079266780245157513500000000000)
      constant := (2410073717956487161401377024922473512718210759) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree056.table
  base := (3457525648460913861941360956397074748761/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20402000000000000000000000000000000000000000
      center := (163216)
      previous := (81608)
      next := (81608)
      square := (2402099897969840630151949836280000000000000)
      linear := (-135190928879440112609682882241930800000000000)
      constant := (1937417087790687253949030211416260159512110961) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 56 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 56 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370805380533144588443/100000000000000000000)
  centralHi := (92701345133286147111/25000000000000000000)
  directionLo := (3741611537343595959/1000000000000000000)
  directionHi := (374161153734359595901/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree057.table
  base := (4736062804381546724619987605220968348361/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (204020)
      previous := (102010)
      next := (102010)
      square := (3002624872462300787689937295350000000000000)
      linear := (-171582512783679702581172385267951000000000000)
      constant := (2499547734068269461384385265963498629371630561) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree057.table
  base := (1184015288777521260756398334047352526449/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12751250000000000000000000000000000000000000
      center := (102010)
      previous := (51005)
      next := (51005)
      square := (1501312436231150393844968647675000000000000)
      linear := (-86003075225664543301598972863969250000000000)
      constant := (1255833435912989594897444778003508586244612498) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 57 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 57 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3741611537343595959/1000000000000000000)
  centralHi := (374161153734359595901/100000000000000000000)
  directionLo := (9437177401616305973/2500000000000000000)
  directionHi := (377487096064652238921/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree058.table
  base := (10326921448566194480598539319673364701057/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (408040)
      previous := (204020)
      next := (204020)
      square := (6005249744924601575379874590700000000000000)
      linear := (-349185139791850651791129050756777000000000000)
      constant := (5181331216346439708534558314716860493315482457) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree058.table
  base := (516345938296205112054459511038660658909/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2550250000000000000000000000000000000000000
      center := (20402)
      previous := (10201)
      next := (10201)
      square := (300262487246230078768993729535000000000000)
      linear := (-17502363980335803244429228865346350000000000)
      constant := (260321370102664051798760212773360352381530709) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 58 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 58 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9437177401616305973/2500000000000000000)
  centralHi := (377487096064652238921/100000000000000000000)
  directionLo := (2974874915581454799/781250000000000000)
  directionHi := (380783989194426214273/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree059.table
  base := (22416409479402359118455036860894120763893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-710410508032683796839826661955304000000000000)
      constant := (10733709341592078232687206255066631550912472493) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree059.table
  base := (22416405117215959980249879932472265388347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-712164516621547913141546526315954000000000000)
      constant := (10785647370394528432806655782227426579226527747) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 59 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 59 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2974874915581454799/781250000000000000)
  centralHi := (380783989194426214273/100000000000000000000)
  directionLo := (96013145310394155677/25000000000000000000)
  directionHi := (384052581241576622709/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree060.table
  base := (4846389887473731142970784814082734168059/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20402000000000000000000000000000000000000000
      center := (163216)
      previous := (81608)
      next := (81608)
      square := (2402099897969840630151949836280000000000000)
      linear := (-144490147296333258019479044479410800000000000)
      constant := (2222266329478815884013015110099512971248369859) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree060.table
  base := (4846389178351764742048350189436825749639/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20402000000000000000000000000000000000000000
      center := (163216)
      previous := (81608)
      next := (81608)
      square := (2402099897969840630151949836280000000000000)
      linear := (-144846894805932739301184779603610800000000000)
      constant := (2233009034204305254162675545981731059472067439) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 60 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 60 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96013145310394155677/25000000000000000000)
  centralHi := (384052581241576622709/100000000000000000000)
  directionLo := (48411698594227770219/12500000000000000000)
  directionHi := (387293588753822161753/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree061.table
  base := (13050230775493194655104742770289991131561/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (408040)
      previous := (204020)
      next := (204020)
      square := (6005249744924601575379874590700000000000000)
      linear := (-367245482465324391677481891419402000000000000)
      constant := (5747764668826602531011702466626537262033053761) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree061.table
  base := (13050229334947526334815427637584677117577/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (408040)
      previous := (204020)
      next := (204020)
      square := (6005249744924601575379874590700000000000000)
      linear := (-368152215718889739935150634860077000000000000)
      constant := (5775524096946718112800917910546330291276402977) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 61 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 61 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48411698594227770219/12500000000000000000)
  centralHi := (387293588753822161753/100000000000000000000)
  directionLo := (15620307941718006277/4000000000000000000)
  directionHi := (195253849271475078463/50000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree062.table
  base := (28021944845552434448549161858136231063141/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-746531193379631276612532343280554000000000000)
      constant := (11886302402426508575785818324758527693075101341) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree062.table
  base := (7005485626266142176758866174677667464007/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (204020)
      previous := (102010)
      next := (102010)
      square := (3002624872462300787689937295350000000000000)
      linear := (-187093597211473815808669660355563500000000000)
      constant := (2985914107338599734987446261557627135800335407) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 62 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 62 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15620307941718006277/4000000000000000000)
  centralHi := (195253849271475078463/50000000000000000000)
  directionLo := (393695569384275072999/100000000000000000000)
  directionHi := (393695569384275073/100000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree063.table
  base := (29996398542474500686891525382271183397897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-758571421828613769870100903722304000000000000)
      constant := (12283650833771570006543462181650008966841947297) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree063.table
  base := (29996396641646676233626451675600873503041/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-760444346254011046599056013124354000000000000)
      constant := (12342869869696327698155579475264143510604521241) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 63 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 63 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (393695569384275072999/100000000000000000000)
  centralHi := (393695569384275073/100000000000000000)
  directionLo := (49607229199152746233/12500000000000000000)
  directionHi := (79371566718644393973/20000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree064.table
  base := (8005955504978423680401185703912415133269/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (204020)
      previous := (102010)
      next := (102010)
      square := (3002624872462300787689937295350000000000000)
      linear := (-192652912569399065781917366041013500000000000)
      constant := (3171893656336252700926497043115350546774477069) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree064.table
  base := (4002977559568098842101425074356416632701/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12751250000000000000000000000000000000000000
      center := (102010)
      previous := (51005)
      next := (51005)
      square := (1501312436231150393844968647675000000000000)
      linear := (-96564287957765853745429173103306750000000000)
      constant := (1593586063595879280200782984568233806070182901) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 64 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 64 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49607229199152746233/12500000000000000000)
  centralHi := (79371566718644393973/20000000000000000000)
  directionLo := (199997549244860980819/50000000000000000000)
  directionHi := (399995098489721961639/100000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree065.table
  base := (532878355958136471252459589433881837539/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 12751250000000000000000000000000000000000000
      center := (102010)
      previous := (51005)
      next := (51005)
      square := (1501312436231150393844968647675000000000000)
      linear := (-97831484840822344548154753075725500000000000)
      constant := (1637259221510191467198397935170042494622882712) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree065.table
  base := (4263026691061868727194663257484502376667/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12751250000000000000000000000000000000000000
      center := (102010)
      previous := (51005)
      next := (51005)
      square := (1501312436231150393844968647675000000000000)
      linear := (-98073032633780326665976344566069250000000000)
      constant := (1645139042707143111233662820253139408744380067) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 65 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 65 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199997549244860980819/50000000000000000000)
  centralHi := (399995098489721961639/100000000000000000000)
  directionLo := (25194246735001581103/6250000000000000000)
  directionHi := (403107947760025297649/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree066.table
  base := (36237576430282947195379827225946401991587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-794692107175561249642806585047554000000000000)
      constant := (13515148269937327143082109887652994246716178987) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree066.table
  base := (9059393853386368494288346225830815802127/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (204020)
      previous := (102010)
      next := (102010)
      square := (3002624872462300787689937295350000000000000)
      linear := (-199163554619589599173047032057663500000000000)
      constant := (3395035341112492140094586708152930901997497527) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 66 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 66 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25194246735001581103/6250000000000000000)
  centralHi := (403107947760025297649/100000000000000000000)
  directionLo := (406196942724580580331/100000000000000000000)
  directionHi := (101549235681145145083/25000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree067.table
  base := (19211953325208285950009896572375086809299/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (408040)
      previous := (204020)
      next := (204020)
      square := (6005249744924601575379874590700000000000000)
      linear := (-403366167812271871450187572744652000000000000)
      constant := (6969399057842483132385433899669683573041659099) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree067.table
  base := (38423905825467231052804516593514825374953/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-808724175886474180056565499932754000000000000)
      constant := (14005775574021661875940723663762045733649895553) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 67 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 67 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (406196942724580580331/100000000000000000000)
  centralHi := (101549235681145145083/25000000000000000000)
  directionLo := (409262623519779910671/100000000000000000000)
  directionHi := (25578913969986244417/6250000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree068.table
  base := (40663205189292612715692051212183315838411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-818772564073526236157943705931054000000000000)
      constant := (14369023306749420918962369176425627004867630611) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree068.table
  base := (10165801130025828983492038057606665180453/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (204020)
      previous := (102010)
      next := (102010)
      square := (3002624872462300787689937295350000000000000)
      linear := (-205198533323647490855235717908713500000000000)
      constant := (3609503741970395061880947128536734091505801053) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 68 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 68 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (409262623519779910671/100000000000000000000)
  centralHi := (25578913969986244417/6250000000000000000)
  directionLo := (206152755100307852147/50000000000000000000)
  directionHi := (82461102040123140859/20000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree069.table
  base := (42955471845587378918081561591349859214827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-830812792522508729415512266372804000000000000)
      constant := (14805823841076988136577876297535598038850450227) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree069.table
  base := (21477735651433097106134784221109375883993/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (408040)
      previous := (204020)
      next := (204020)
      square := (6005249744924601575379874590700000000000000)
      linear := (-416432045351352873392660121668477000000000000)
      constant := (7438429772022368118313855415325127743392612593) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 69 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 69 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (206152755100307852147/50000000000000000000)
  centralHi := (82461102040123140859/20000000000000000000)
  directionLo := (415326103770623756171/100000000000000000000)
  directionHi := (103831525942655939043/25000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree070.table
  base := (45300706458811021199875267005215013362547/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-842853020971491222673080826814554000000000000)
      constant := (15249199717030510964833488665386248351311341947) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree070.table
  base := (22650353009374774389815242694922719817897/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (408040)
      previous := (204020)
      next := (204020)
      square := (6005249744924601575379874590700000000000000)
      linear := (-422467024055410765074848807519527000000000000)
      constant := (7661154650464955201216492040316949164862367297) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 70 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 70 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (415326103770623756171/100000000000000000000)
  centralHi := (103831525942655939043/25000000000000000000)
  directionLo := (209162443572444336607/50000000000000000000)
  directionHi := (83664977428977734643/20000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree071.table
  base := (47698908901097053575179501329844231979701/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-854893249420473715930649387256304000000000000)
      constant := (15699150933305623380187104991847321635424929901) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree071.table
  base := (47698908544349261320005748991583999755733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-857004005518937313514074986741154000000000000)
      constant := (15774364237278257333997631647310211381508232333) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 71 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 71 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (209162443572444336607/50000000000000000000)
  centralHi := (83664977428977734643/20000000000000000000)
  directionLo := (84260465210270648443/20000000000000000000)
  directionHi := (52662790756419155277/12500000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree072.table
  base := (50150079070639518944125300313609048022623/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-866933477869456209188217947698054000000000000)
      constant := (16155677488863802814262961972587955898878777223) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree072.table
  base := (6268759847686198439929648457965670960887/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12751250000000000000000000000000000000000000
      center := (102010)
      previous := (51005)
      next := (51005)
      square := (1501312436231150393844968647675000000000000)
      linear := (-108634245365881637109806544805406750000000000)
      constant := (2029128044011035782946870777794222309472008287) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 72 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 72 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84260465210270648443/20000000000000000000)
  centralHi := (52662790756419155277/12500000000000000000)
  directionLo := (53032358734399378739/12500000000000000000)
  directionHi := (424258869875195029913/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree073.table
  base := (26327108443223670451922886668146966603877/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (408040)
      previous := (204020)
      next := (204020)
      square := (6005249744924601575379874590700000000000000)
      linear := (-439486853159219351222893254069902000000000000)
      constant := (8309389691439429648337707228195666268826149277) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree073.table
  base := (5265421665213178435463908398449157710051/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10201000000000000000000000000000000000000000
      center := (81608)
      previous := (40804)
      next := (40804)
      square := (1201049948984920315075974918140000000000000)
      linear := (-88114392033516888024282973014535400000000000)
      constant := (1669828964456392397358445020234504257800230251) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 73 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 73 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53032358734399378739/12500000000000000000)
  centralHi := (424258869875195029913/100000000000000000000)
  directionLo := (26699684528162806211/6250000000000000000)
  directionHi := (427194952450604899377/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree074.table
  base := (27605661142075834789557847219792083786467/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (408040)
      previous := (204020)
      next := (204020)
      square := (6005249744924601575379874590700000000000000)
      linear := (-445506967383710597851677534290777000000000000)
      constant := (8544228307347083094923644956628341546705749867) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree074.table
  base := (27605661047153662933035679343574964720203/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (408040)
      previous := (204020)
      next := (204020)
      square := (6005249744924601575379874590700000000000000)
      linear := (-446606938871642331803603550923727000000000000)
      constant := (8585080057036514765356407619342031715110790803) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 74 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 74 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26699684528162806211/6250000000000000000)
  centralHi := (427194952450604899377/100000000000000000000)
  directionLo := (43011099280391740877/10000000000000000000)
  directionHi := (430110992803917408771/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree075.table
  base := (578213952126550075503858167209543657051/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5100500000000000000000000000000000000000000
      center := (40804)
      previous := (20402)
      next := (20402)
      square := (600524974492460157537987459070000000000000)
      linear := (-45152708160820184448046181451165200000000000)
      constant := (878235459189423896130088323776567305477886255) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree075.table
  base := (28910697529434840487329721205725849053403/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (408040)
      previous := (204020)
      next := (204020)
      square := (6005249744924601575379874590700000000000000)
      linear := (-452641917575700223485792236774777000000000000)
      constant := (8824317880057129585711210824663471886193764003) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 75 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 75 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43011099280391740877/10000000000000000000)
  centralHi := (430110992803917408771/100000000000000000000)
  directionLo := (54125924481462151087/12500000000000000000)
  directionHi := (433007395851697208697/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree076.table
  base := (15121108907863314363376904427565767350311/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (204020)
      previous := (102010)
      next := (102010)
      square := (3002624872462300787689937295350000000000000)
      linear := (-228773597916346545554623047366263500000000000)
      constant := (4511884272437153049431791266374352142740522511) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree076.table
  base := (60484435506900044373732014361627953723117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-917353792559516230335961845251654000000000000)
      constant := (18133716582290602162779915290836044755929516517) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 76 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 76 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54125924481462151087/12500000000000000000)
  centralHi := (433007395851697208697/100000000000000000000)
  directionLo := (435884553057074181431/100000000000000000000)
  directionHi := (54485569132134272679/12500000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree077.table
  base := (63200443508495695439763465133066127501667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-927134620114368675476060749906804000000000000)
      constant := (18536940332247619581242717116323265691644505067) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree077.table
  base := (63200443407635503678053722236208652568423/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-929423749967632013700339216953754000000000000)
      constant := (18625402580288246035543510334384070464850483023) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 77 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 77 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (435884553057074181431/100000000000000000000)
  centralHi := (54485569132134272679/12500000000000000000)
  directionLo := (87748568609467865027/20000000000000000000)
  directionHi := (27421427690458707821/6250000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree078.table
  base := (515386084519335525701011327123154254441/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 12751250000000000000000000000000000000000000
      center := (102010)
      previous := (51005)
      next := (51005)
      square := (1501312436231150393844968647675000000000000)
      linear := (-117396856070418896091703663793569250000000000)
      constant := (2379114863878417443592009916387535244792842256) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree078.table
  base := (16492354684203641560000793950191564734273/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (204020)
      previous := (102010)
      next := (102010)
      square := (3002624872462300787689937295350000000000000)
      linear := (-235373426843936949266179147163963500000000000)
      constant := (4780923438464924825803705244547406401854318873) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 78 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 78 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (87748568609467865027/20000000000000000000)
  centralHi := (27421427690458707821/6250000000000000000)
  directionLo := (110395658048889976843/25000000000000000000)
  directionHi := (441582632195559907373/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree079.table
  base := (687913615414606880138040522755900308569/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5100500000000000000000000000000000000000000
      center := (40804)
      previous := (20402)
      next := (20402)
      square := (600524974492460157537987459070000000000000)
      linear := (-47560753850616683099559893539515200000000000)
      constant := (976773641294223142749416330393549726488561845) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree079.table
  base := (68791361475356094400584733298364477164377/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-953563664783863580429093960357954000000000000)
      constant := (19628590102810315280534432680690203031553809777) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 79 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 79 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110395658048889976843/25000000000000000000)
  centralHi := (441582632195559907373/100000000000000000000)
  directionLo := (444404275168743233061/100000000000000000000)
  directionHi := (222202137584371616531/50000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree080.table
  base := (69986593419734462614324005856529283021/9765625000000000000000000000000000000)
  polynomial :=
    { denominator := 12751250000000000000000000000000000000000000
      center := (102010)
      previous := (51005)
      next := (51005)
      square := (1501312436231150393844968647675000000000000)
      linear := (-120406913182664519406095803904006750000000000)
      constant := (2505575259582424576330423153200121767660444288) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree080.table
  base := (71666271608304576737528767482268739053483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-965633622191979363793471332060054000000000000)
      constant := (20140091626987532795483772974341863407084580083) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 80 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 80 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (444404275168743233061/100000000000000000000)
  centralHi := (222202137584371616531/50000000000000000000)
  directionLo := (223604057722435442723/50000000000000000000)
  directionHi := (447208115444870885447/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree081.table
  base := (74594149167285876585949505000168330683123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-975295533910298648506334991673804000000000000)
      constant := (20560306663227369571127016045988135266298537723) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree081.table
  base := (74594149123988148683797176203223890906833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-977703579600095147157848703762154000000000000)
      constant := (20658198326272287157614486179120054911140603433) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 81 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 81 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223604057722435442723/50000000000000000000)
  centralHi := (447208115444870885447/100000000000000000000)
  directionLo := (449994485800937206843/100000000000000000000)
  directionHi := (112498621450234301711/25000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree082.table
  base := (77574994048379905814248931112248490684431/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-987335762359281141763903552115554000000000000)
      constant := (21082586585491327965673169908981901853471880631) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree082.table
  base := (38787497006673275364183512934463280368291/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (408040)
      previous := (204020)
      next := (204020)
      square := (6005249744924601575379874590700000000000000)
      linear := (-494886768504105465261113037732127000000000000)
      constant := (10591455100286077329827313674724845423036936491) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 82 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 82 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (449994485800937206843/100000000000000000000)
  centralHi := (112498621450234301711/25000000000000000000)
  directionLo := (452763708773955059281/100000000000000000000)
  directionHi := (226381854386977529641/50000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree083.table
  base := (2519025196804282355365867663032045157013/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 12751250000000000000000000000000000000000000
      center := (102010)
      previous := (51005)
      next := (51005)
      square := (1501312436231150393844968647675000000000000)
      linear := (-124921998851032954377684014069663000000000000)
      constant := (2701430230422032799053897743262610898711758452) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree083.table
  base := (16121761253878964240842545993516380681677/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20402000000000000000000000000000000000000000
      center := (163216)
      previous := (81608)
      next := (81608)
      square := (2402099897969840630151949836280000000000000)
      linear := (-200368698883265342777320689433270800000000000)
      constant := (4342845449963176341527773695464790399333787077) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 83 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 83 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (452763708773955059281/100000000000000000000)
  centralHi := (226381854386977529641/50000000000000000000)
  directionLo := (455516097096736748897/100000000000000000000)
  directionHi := (227758048548368374449/50000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree084.table
  base := (16739117181944221688951765486970060987793/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20402000000000000000000000000000000000000000
      center := (163216)
      previous := (81608)
      next := (81608)
      square := (2402099897969840630151949836280000000000000)
      linear := (-202283243851449225655808134599810800000000000)
      constant := (4429374487364935683149170671078558592136476393) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree084.table
  base := (83695585886795398812317991075229699610067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-1013913451824442497250980818868454000000000000)
      constant := (22252149473949019838755944312721020165722293467) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 84 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 84 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (455516097096736748897/100000000000000000000)
  centralHi := (227758048548368374449/50000000000000000000)
  directionLo := (458251954110116821949/100000000000000000000)
  directionHi := (9165039082202336439/2000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree085.table
  base := (21708833220014633923352931450703721618901/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (204020)
      previous := (102010)
      next := (102010)
      square := (3002624872462300787689937295350000000000000)
      linear := (-255864111926557155384152308360201000000000000)
      constant := (5672219591448245287689985537110998195484409101) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree085.table
  base := (86835332861516805406372936021557165798101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-1025983409232558280615358190570554000000000000)
      constant := (22796676872930443944435347839430534648306428301) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 85 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 85 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (458251954110116821949/100000000000000000000)
  centralHi := (9165039082202336439/2000000000000000000)
  directionLo := (460971574153154833913/100000000000000000000)
  directionHi := (230485787076577416957/50000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree086.table
  base := (18005609441111094885564510042695242770593/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20402000000000000000000000000000000000000000
      center := (163216)
      previous := (81608)
      next := (81608)
      square := (2402099897969840630151949836280000000000000)
      linear := (-207099335231042222958835558776510800000000000)
      constant := (4647491926049718041638870119649692171502819193) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree086.table
  base := (45014023595280735063311135931549164962921/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (408040)
      previous := (204020)
      next := (204020)
      square := (6005249744924601575379874590700000000000000)
      linear := (-519026683320337031989867781136327000000000000)
      constant := (11673904723364787902168357657068099531786757121) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 86 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 86 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (460971574153154833913/100000000000000000000)
  centralHi := (230485787076577416957/50000000000000000000)
  directionLo := (46367524293273890277/10000000000000000000)
  directionHi := (463675242932738902771/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree087.table
  base := (11659216110484026959294878609893549054231/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12751250000000000000000000000000000000000000
      center := (102010)
      previous := (51005)
      next := (51005)
      square := (1501312436231150393844968647675000000000000)
      linear := (-130942113075524201006468294290538000000000000)
      constant := (2974077028770954777101131987537501672027210431) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree087.table
  base := (18654745774349752761799305519999396495093/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20402000000000000000000000000000000000000000
      center := (163216)
      previous := (81608)
      next := (81608)
      square := (2402099897969840630151949836280000000000000)
      linear := (-210024664809757969468822586794950800000000000)
      constant := (4781109439064834164071474812633696043646443693) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 87 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 87 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46367524293273890277/10000000000000000000)
  centralHi := (463675242932738902771/100000000000000000000)
  directionLo := (466363237873903767959/100000000000000000000)
  directionHi := (11659080946847594199/2500000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree088.table
  base := (19314475582668655513449937959576686106179/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20402000000000000000000000000000000000000000
      center := (163216)
      previous := (81608)
      next := (81608)
      square := (2402099897969840630151949836280000000000000)
      linear := (-211915426610635220261862982953210800000000000)
      constant := (4870869633106627119218264653741355774969131979) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree088.table
  base := (96572377903542115152676432752235177112717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-1062193281456905630708490305676854000000000000)
      constant := (24469890118698554428657666708360715041726826117) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 88 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 88 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (466363237873903767959/100000000000000000000)
  centralHi := (11659080946847594199/2500000000000000000)
  directionLo := (469035828452079193543/100000000000000000000)
  directionHi := (58629478556509899193/12500000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree089.table
  base := (99923994292834011830035950518733582104227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-1071617361502158594566883475207804000000000000)
      constant := (24922655436333507798972998703886639396045219627) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree089.table
  base := (49961997142455659591707170670037296279653/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (408040)
      previous := (204020)
      next := (204020)
      square := (6005249744924601575379874590700000000000000)
      linear := (-537131619432510707036433838689477000000000000)
      constant := (12520419108421108754147646506536796459348740253) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 89 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 89 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (469035828452079193543/100000000000000000000)
  centralHi := (58629478556509899193/12500000000000000000)
  directionLo := (235846638254197495569/50000000000000000000)
  directionHi := (471693276508394991139/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree090.table
  base := (103328578021626375436058144528817424581639/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-1083657589951141087824452035649554000000000000)
      constant := (25497538042561430068539126947741691548157299439) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree090.table
  base := (6458036125951433586286595732010922931071/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12751250000000000000000000000000000000000000
      center := (102010)
      previous := (51005)
      next := (51005)
      square := (1501312436231150393844968647675000000000000)
      linear := (-135791649534142149679655631135131750000000000)
      constant := (3202298936218587294115170023967723724639710542) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 90 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 90 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (235846638254197495569/50000000000000000000)
  centralHi := (471693276508394991139/100000000000000000000)
  directionLo := (94867167309817380479/20000000000000000000)
  directionHi := (118583959137271725599/25000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree091.table
  base := (53393064549663997353701928930576736880607/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (408040)
      previous := (204020)
      next := (204020)
      square := (6005249744924601575379874590700000000000000)
      linear := (-547848909200061790541010298045652000000000000)
      constant := (13039497992106449900450661732697378605419072007) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree091.table
  base := (53393064547076558976060736680362402415101/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (408040)
      previous := (204020)
      next := (204020)
      square := (6005249744924601575379874590700000000000000)
      linear := (-549201576840626490400811210391577000000000000)
      constant := (13101274968707346675202488582327563367036445301) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 91 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 91 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94867167309817380479/20000000000000000000)
  centralHi := (118583959137271725599/25000000000000000000)
  directionLo := (476963756029972363493/100000000000000000000)
  directionHi := (238481878014986181747/50000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree092.table
  base := (53855784924706947440354541829366835161/4882812500000000000000000000000000000)
  polynomial :=
    { denominator := 12751250000000000000000000000000000000000000
      center := (102010)
      previous := (51005)
      next := (51005)
      square := (1501312436231150393844968647675000000000000)
      linear := (-138467255856138259292448644566631750000000000)
      constant := (3333378657660812329487348342949395372882204416) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree092.table
  base := (110296647521618306458842491702375757245181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-1110473111089368764165999792485254000000000000)
      constant := (26793313559839350161912072071388861099658091381) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 92 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 92 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (476963756029972363493/100000000000000000000)
  centralHi := (238481878014986181747/50000000000000000000)
  directionLo := (239788637813448069871/50000000000000000000)
  directionHi := (479577275626896139743/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree093.table
  base := (113860133301098678653394537320707969031501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-1119778275298088567597157716974804000000000000)
      constant := (27261637873782806013447081338036640117090341701) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree093.table
  base := (56930066648860114543720555329354322688997/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (408040)
      previous := (204020)
      next := (204020)
      square := (6005249744924601575379874590700000000000000)
      linear := (-561271534248742273765188582093677000000000000)
      constant := (13695341178511853248136547674233520445750458397) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 93 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 93 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239788637813448069871/50000000000000000000)
  centralHi := (479577275626896139743/100000000000000000000)
  directionLo := (241088314746491198679/50000000000000000000)
  directionHi := (482176629492982397359/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree094.table
  base := (11747658642543155340014172219479361853041/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10201000000000000000000000000000000000000000
      center := (81608)
      previous := (40804)
      next := (40804)
      square := (1201049948984920315075974918140000000000000)
      linear := (-113181850374707106085472627741655400000000000)
      constant := (2786282182170393362017615742646224970262871241) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree094.table
  base := (117476586422702259514068124353423872127051/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-1134613025905600330894754535889454000000000000)
      constant := (27994656328970245008358461246745533919568047251) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 94 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 94 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (241088314746491198679/50000000000000000000)
  centralHi := (482176629492982397359/100000000000000000000)
  directionLo := (121190511375867864997/25000000000000000000)
  directionHi := (484762045503471459989/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree095.table
  base := (121146006899119483805039377146394276021687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-1143858732196053554112294837858304000000000000)
      constant := (28470581105053156295428129513340308634697229087) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree095.table
  base := (30286501724228715593187347101152056504283/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (204020)
      previous := (102010)
      next := (102010)
      square := (3002624872462300787689937295350000000000000)
      linear := (-286670745828429028564782976897888500000000000)
      constant := (7151308868920635196974966879846110878400190883) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 95 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 95 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121190511375867864997/25000000000000000000)
  centralHi := (484762045503471459989/100000000000000000000)
  directionLo := (487333745488865819427/100000000000000000000)
  directionHi := (121833436372216454857/25000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree096.table
  base := (124868394722568884716653077312187707039697/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-1155898960645036047369863398300054000000000000)
      constant := (29084915723834619877073215030640066799511949097) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree096.table
  base := (124868394720788271314670983409153935888347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-1158752940721831897623509279293654000000000000)
      constant := (29222419797164982648373063374552667299997027747) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 96 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 96 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (487333745488865819427/100000000000000000000)
  centralHi := (121833436372216454857/25000000000000000000)
  directionLo := (244945972728530259497/50000000000000000000)
  directionHi := (97978389091412103799/20000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree097.table
  base := (16080468737031116073023946733975184044609/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12751250000000000000000000000000000000000000
      center := (102010)
      previous := (51005)
      next := (51005)
      square := (1501312436231150393844968647675000000000000)
      linear := (-145992398636752317578428994842725500000000000)
      constant := (3713228209756638799158224056143113118064056409) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree097.table
  base := (16080468736851366382678669321248623639247/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12751250000000000000000000000000000000000000
      center := (102010)
      previous := (51005)
      next := (51005)
      square := (1501312436231150393844968647675000000000000)
      linear := (-146352862266243460123485831374469250000000000)
      constant := (3730776161677819151797881768720659209743958647) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 97 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 97 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell088.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244945972728530259497/50000000000000000000)
  centralHi := (97978389091412103799/20000000000000000000)
  directionLo := (7694325871954491107/1562500000000000000)
  directionHi := (492436855805087430849/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 405
  qDenominator := 808
  table := BinomialMassData.Q405_808.Degree098.table
  base := (132472072420673712056738064917329660886119/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-1179979417543001033885000519183554000000000000)
      constant := (30333310967713872143923159472592274870699299919) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q405_808.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 203
  qDenominator := 404
  table := BinomialMassData.Q203_404.Degree098.table
  base := (132472072419512529529956903458079888730491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (816080)
      previous := (408040)
      next := (408040)
      square := (12010499489849203150759749181400000000000000)
      linear := (-1182892855538063464352264022697854000000000000)
      constant := (30476603964460655832370467273447691944939738691) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q203_404.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 98 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 98 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage80KernelData.Cell088.Kernel098
