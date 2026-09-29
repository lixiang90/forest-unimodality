import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage170KernelData.Cell003.Parameters
import ForestUnimodality.BinomialMassData.Q1_4.Batch250_299
import ForestUnimodality.BinomialMassData.Q9_35.Batch250_299

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel250
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217058403186071245273/50000000000000000000)
  centralHi := (434116806372142490547/100000000000000000000)
  directionLo := (6796736896083765141/1562500000000000000)
  directionHi := (17399646453974438761/4000000000000000000)

def endpointA : IntegerEndpointWitness 250 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree250.table
  base := (-3377275496041549610503667094824953941283/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-43603925815619797023980908180000000000000)
      constant := (1321180037238290069995764908866400368469736) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 250 interval.damping) (curvature.centralUpper 250 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree250.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 250 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree250.table
  base := (-3377275496041831035528894615400890297591/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-2747855095053810999157495326900000000000000)
      constant := (85760309023042024930832101640953563754180410) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 250 interval.damping) (curvature.centralUpper 250 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree250.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 250 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 250 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell003.Kernel250

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel251
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6796736896083765141/1562500000000000000)
  centralHi := (17399646453974438761/4000000000000000000)
  directionLo := (435863762349410416613/100000000000000000000)
  directionHi := (217931881174705208307/50000000000000000000)

def endpointA : IntegerEndpointWitness 251 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree251.table
  base := (-3357823295157348685587938033705496083031/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-43780187847270307724412141782000000000000)
      constant := (1332258669053224940488639872600606031335752) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 251 interval.damping) (curvature.centralUpper 251 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree251.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 251 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree251.table
  base := (-6715646590315183867030832684166496417879/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-2758959603047793173284663043826000000000000)
      constant := (86477859634088365484418412071115408377619645) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 251 interval.damping) (curvature.centralUpper 251 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree251.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 251 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 251 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell003.Kernel251

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel252
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (435863762349410416613/100000000000000000000)
  centralHi := (217931881174705208307/50000000000000000000)
  directionLo := (436734619885693118087/100000000000000000000)
  directionHi := (54591827485711639761/12500000000000000000)

def endpointA : IntegerEndpointWitness 252 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree252.table
  base := (-1335256392164160551761856678186691972839/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-43956449878920818424843375384000000000000)
      constant := (1343383207286974409706763182952266160543220) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 252 interval.damping) (curvature.centralUpper 252 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree252.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 252 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree252.table
  base := (-6676281960821223252412111937743611476171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (702)
      previous := (243)
      next := (0)
      square := (3084585553883937257546588035000000000000)
      linear := (-395723444434539335344547251536000000000000)
      constant := (12456911206548598214563812959225373598334015) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 252 interval.damping) (curvature.centralUpper 252 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree252.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 252 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 252 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell003.Kernel252

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel253
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (436734619885693118087/100000000000000000000)
  centralHi := (54591827485711639761/12500000000000000000)
  directionLo := (218801872183499830781/50000000000000000000)
  directionHi := (437603744366999661563/100000000000000000000)

def endpointA : IntegerEndpointWitness 253 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree253.table
  base := (-6636457115259364248455869688790774256341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-44132711910571329125274608986000000000000)
      constant := (1354553651892906682191941585807086902974636) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 253 interval.damping) (curvature.centralUpper 253 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree253.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 253 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree253.table
  base := (-3318228557629863844556786803335819329453/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-2781168619035757521538998477678000000000000)
      constant := (87921865455441293855248510650631248528568030) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 253 interval.damping) (curvature.centralUpper 253 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree253.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 253 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 253 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell003.Kernel253

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel254
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (218801872183499830781/50000000000000000000)
  centralHi := (437603744366999661563/100000000000000000000)
  directionLo := (438471146098960451669/100000000000000000000)
  directionHi := (43847114609896045167/10000000000000000000)

def endpointA : IntegerEndpointWitness 254 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree254.table
  base := (-6596172065175825668924997525471316252369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-44308973942221839825705842588000000000000)
      constant := (1365770002824839982628937630907114734990524) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 254 interval.damping) (curvature.centralUpper 254 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree254.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 254 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree254.table
  base := (-1649043016294034948308811017964648410959/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-2792273127029739695666166194604000000000000)
      constant := (88648320660063051103379365415953844557260180) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 254 interval.damping) (curvature.centralUpper 254 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree254.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 254 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 254 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell003.Kernel254

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel255
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (438471146098960451669/100000000000000000000)
  centralHi := (43847114609896045167/10000000000000000000)
  directionLo := (878673670570942861/200000000000000000)
  directionHi := (439336835285471430501/100000000000000000000)

def endpointA : IntegerEndpointWitness 255 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree255.table
  base := (-6555426822004638503883945448535889421179/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-44485235973872350526137076190000000000000)
      constant := (1377032260037036505083082204062106442315284) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 255 interval.damping) (curvature.centralUpper 255 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree255.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 255 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree255.table
  base := (-6555426822004909999962288990860964940459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-2803377635023721869793333911530000000000000)
      constant := (89377744056904018889718889424444063589587545) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 255 interval.damping) (curvature.centralUpper 255 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree255.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 255 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 255 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell003.Kernel255

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel256
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (878673670570942861/200000000000000000)
  centralHi := (439336835285471430501/100000000000000000000)
  directionLo := (440200822030094564299/100000000000000000000)
  directionHi := (4402008220300945643/1000000000000000000)

def endpointA : IntegerEndpointWitness 256 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree256.table
  base := (-6514221397070748556201582147174260268117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-44661498005522861226568309792000000000000)
      constant := (1388340423484196466342899830515302958927532) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 256 interval.damping) (curvature.centralUpper 256 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree256.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 256 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree256.table
  base := (-407138837316936450355243009842539450241/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-2814482143017704043920501628456000000000000)
      constant := (90110135643189585714651733626620445355055280) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 256 interval.damping) (curvature.centralUpper 256 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree256.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 256 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 256 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell003.Kernel256

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel257
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (440200822030094564299/100000000000000000000)
  centralHi := (4402008220300945643/1000000000000000000)
  directionLo := (55132889542179204951/12500000000000000000)
  directionHi := (441063116337433639609/100000000000000000000)

def endpointA : IntegerEndpointWitness 257 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree257.table
  base := (-6472555801591057131171462656910600802241/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-44837760037173371926999543394000000000000)
      constant := (1399694493121452261187216290124607596791036) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 257 interval.damping) (curvature.centralUpper 257 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree257.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 257 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree257.table
  base := (-3236277900795629965998515479496813562527/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-2825586651011686218047669345382000000000000)
      constant := (90845495416171610950386635622600361354361770) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 257 interval.damping) (curvature.centralUpper 257 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree257.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 257 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 257 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell003.Kernel257

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel258
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55132889542179204951/12500000000000000000)
  centralHi := (441063116337433639609/100000000000000000000)
  directionLo := (441923728114485898847/100000000000000000000)
  directionHi := (13810116503577684339/3125000000000000000)

def endpointA : IntegerEndpointWitness 258 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree258.table
  base := (-1286086009335171454036741681854167103581/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-45014022068823882627430776996000000000000)
      constant := (1411094468904362717450471097163916657928380) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 258 interval.damping) (curvature.centralUpper 258 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree258.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 258 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree258.table
  base := (-6430430046676032542758467784509535172523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-2836691159005668392174837062308000000000000)
      constant := (91583823373128072967778691567051963882731865) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 258 interval.damping) (curvature.centralUpper 258 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree258.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 258 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 258 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell003.Kernel258

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel259
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (441923728114485898847/100000000000000000000)
  centralHi := (13810116503577684339/3125000000000000000)
  directionLo := (1729619793640507937/390625000000000000)
  directionHi := (442782667171970031873/100000000000000000000)

def endpointA : IntegerEndpointWitness 259 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree259.table
  base := (-3193922071665122776685660556180216028883/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-45190284100474393327862010598000000000000)
      constant := (1422540350788907448812132244800808271768936) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 259 interval.damping) (curvature.centralUpper 259 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree259.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 259 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree259.table
  base := (-6387844143330397032359174981403733024397/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (702)
      previous := (243)
      next := (0)
      square := (3084585553883937257546588035000000000000)
      linear := (-406827952428521509471714968462000000000000)
      constant := (13189302787337531892600301750695469344146105) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 259 interval.damping) (curvature.centralUpper 259 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree259.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 259 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 259 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell003.Kernel259

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel260
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1729619793640507937/390625000000000000)
  centralHi := (442782667171970031873/100000000000000000000)
  directionLo := (443639943225631027071/100000000000000000000)
  directionHi := (3465937056450242399/781250000000000000)

def endpointA : IntegerEndpointWitness 260 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree260.table
  base := (-1586199525613877494253871948427013304959/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-45366546132124904028293244200000000000000)
      constant := (1434032138731481303287074984925167787120656) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 260 interval.damping) (curvature.centralUpper 260 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree260.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 260 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree260.table
  base := (-1268959620491128178140407056479538183919/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-2858900174993632740429172496160000000000000)
      constant := (93069383828204746356630691416532565724699225) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 260 interval.damping) (curvature.centralUpper 260 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree260.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 260 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 260 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell003.Kernel260

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel261
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (443639943225631027071/100000000000000000000)
  centralHi := (3465937056450242399/781250000000000000)
  directionLo := (444495565897522372927/100000000000000000000)
  directionHi := (6945243217148787077/1562500000000000000)

def endpointA : IntegerEndpointWitness 261 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree261.table
  base := (-6301291934850494399145664055827521403641/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-45542808163775414728724477802000000000000)
      constant := (1445569832688888905443181495126939914385436) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 261 interval.damping) (curvature.centralUpper 261 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree261.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 261 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree261.table
  base := (-6301291934850607538055702178408782720027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-2870004682987614914556340213086000000000000)
      constant := (93816616321008425655098608946770048233593385) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 261 interval.damping) (curvature.centralUpper 261 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree261.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 261 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 261 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell003.Kernel261

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel262
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (444495565897522372927/100000000000000000000)
  centralHi := (6945243217148787077/1562500000000000000)
  directionLo := (44534954471726608873/10000000000000000000)
  directionHi := (445349544717266088731/100000000000000000000)

def endpointA : IntegerEndpointWitness 262 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree262.table
  base := (-6257325651212940034748975659336510572627/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-45719070195425925429155711404000000000000)
      constant := (1457153432618339290420503272363653957709492) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 262 interval.damping) (curvature.centralUpper 262 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree262.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 262 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree262.table
  base := (-6257325651213037810971869167299213785161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-2881109190981597088683507930012000000000000)
      constant := (94566816987152814638650699938604492622635555) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 262 interval.damping) (curvature.centralUpper 262 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree262.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 262 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 262 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell003.Kernel262

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel263
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44534954471726608873/10000000000000000000)
  centralHi := (445349544717266088731/100000000000000000000)
  directionLo := (89240377824658210237/20000000000000000000)
  directionHi := (223100944561645525593/50000000000000000000)

def endpointA : IntegerEndpointWitness 263 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree263.table
  base := (-1242579852428160894074073323241119378219/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-45895332227076436129586945006000000000000)
      constant := (1468782938477440627872860540587427612435620) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 263 interval.damping) (curvature.centralUpper 263 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree263.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 263 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree263.table
  base := (-6212899262140888968850761355350650642789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-2892213698975579262810675646938000000000000)
      constant := (95319985824041413778733909240996890592516695) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 263 interval.damping) (curvature.centralUpper 263 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree263.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 263 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 263 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell003.Kernel263

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel264
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89240377824658210237/20000000000000000000)
  centralHi := (223100944561645525593/50000000000000000000)
  directionLo := (447052608464050072107/100000000000000000000)
  directionHi := (111763152116012518027/25000000000000000000)

def endpointA : IntegerEndpointWitness 264 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree264.table
  base := (-1233602555626711731306777768602935782927/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-46071594258726946830018178608000000000000)
      constant := (1480458350224195033998157092131941284341460) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 264 interval.damping) (curvature.centralUpper 264 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree264.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 264 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree264.table
  base := (-3084006389066815839707598654338544288279/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-2903318206969561436937843363864000000000000)
      constant := (96076122829101852761756146305249313298743290) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 264 interval.damping) (curvature.centralUpper 264 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree264.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 264 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 264 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell003.Kernel264

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel265
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (447052608464050072107/100000000000000000000)
  centralHi := (111763152116012518027/25000000000000000000)
  directionLo := (223950855999608085589/50000000000000000000)
  directionHi := (447901711999216171179/100000000000000000000)

def endpointA : IntegerEndpointWitness 265 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree265.table
  base := (-6122666209593462325369436652503873243247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-46247856290377457530449412210000000000000)
      constant := (1492179667816993469867873349746234507027012) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 265 interval.damping) (curvature.centralUpper 265 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree265.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 265 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree265.table
  base := (-1530666552398381357582613718853364780397/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-2914422714963543611065011080790000000000000)
      constant := (96835227999785578013239418058568702515210940) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 265 interval.damping) (curvature.centralUpper 265 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree265.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 265 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 265 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell003.Kernel265

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel266
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223950855999608085589/50000000000000000000)
  centralHi := (447901711999216171179/100000000000000000000)
  directionLo := (448749208900858476759/100000000000000000000)
  directionHi := (11218730222521461919/2500000000000000000)

def endpointA : IntegerEndpointWitness 266 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree266.table
  base := (-3038429783413409135096346944689926930867/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-46424118322027968230880645812000000000000)
      constant := (1503946891214610724308746578051480584553064) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 266 interval.damping) (curvature.centralUpper 266 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree266.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 266 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree266.table
  base := (-759607445853359100448814315550766153887/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (702)
      previous := (243)
      next := (0)
      square := (3084585553883937257546588035000000000000)
      linear := (-417932460422503683598882685388000000000000)
      constant := (13942471619081077914370742755155385476911640) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 266 interval.damping) (curvature.centralUpper 266 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree266.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 266 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 266 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell003.Kernel266

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel267
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (448749208900858476759/100000000000000000000)
  centralHi := (11218730222521461919/2500000000000000000)
  directionLo := (7024923566478096519/1562500000000000000)
  directionHi := (449595108254598177217/100000000000000000000)

def endpointA : IntegerEndpointWitness 267 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree267.table
  base := (-6030592860045205913278541448913743043089/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-46600380353678478931311879414000000000000)
      constant := (1515760020376200479631677253466595027827644) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 267 interval.damping) (curvature.centralUpper 267 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree267.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 267 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree267.table
  base := (-6030592860045253038800925165306507387913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-2936631730951507959319346514642000000000000)
      constant := (98362342827945918010120130504941705689961315) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 267 interval.damping) (curvature.centralUpper 267 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree267.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 267 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 267 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell003.Kernel267

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel268
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7024923566478096519/1562500000000000000)
  centralHi := (449595108254598177217/100000000000000000000)
  directionLo := (225219709530372467419/50000000000000000000)
  directionHi := (450439419060744934839/100000000000000000000)

def endpointA : IntegerEndpointWitness 268 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree268.table
  base := (-5983866099366694578024062536804204296919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-46776642385328989631743113016000000000000)
      constant := (1527619055261290458543077043168783182812324) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 268 interval.damping) (curvature.centralUpper 268 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree268.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 268 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree268.table
  base := (-2991933049683367650729648399402370132943/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-2947736238945490133446514231568000000000000)
      constant := (99130352480441768896267297264961638634857930) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 268 interval.damping) (curvature.centralUpper 268 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree268.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 268 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 268 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell003.Kernel268

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel269
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (225219709530372467419/50000000000000000000)
  centralHi := (450439419060744934839/100000000000000000000)
  directionLo := (14102567194856692639/3125000000000000000)
  directionHi := (451282150235414164449/100000000000000000000)

def endpointA : IntegerEndpointWitness 269 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree269.table
  base := (-2968339647408518435896534696580797702749/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-46952904416979500332174346618000000000000)
      constant := (1539523995829777650613490698197603618378008) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 269 interval.damping) (curvature.centralUpper 269 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree269.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 269 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree269.table
  base := (-5936679294817072062443072033099454549667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-2958840746939472307573681948494000000000000)
      constant := (99901330288598788703671726127138833635331585) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 269 interval.damping) (curvature.centralUpper 269 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree269.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 269 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 269 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell003.Kernel269

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel270
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14102567194856692639/3125000000000000000)
  centralHi := (451282150235414164449/100000000000000000000)
  directionLo := (452123310611625569043/100000000000000000000)
  directionHi := (113030827652906392261/25000000000000000000)

def endpointA : IntegerEndpointWitness 270 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree270.table
  base := (-5889032456330842576181465469240377867399/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-47129166448630011032605580220000000000000)
      constant := (1551474842041923616716534604748038488530404) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 270 interval.damping) (curvature.centralUpper 270 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree270.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 270 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree270.table
  base := (-1472258114082718246343185674570409816037/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-2969945254933454481700849665420000000000000)
      constant := (100675276249982998064746396593100998380283740) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 270 interval.damping) (curvature.centralUpper 270 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree270.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 270 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 270 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell003.Kernel270

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel271
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (452123310611625569043/100000000000000000000)
  centralHi := (113030827652906392261/25000000000000000000)
  directionLo := (113240727235095828831/25000000000000000000)
  directionHi := (18118516357615332613/4000000000000000000)

def endpointA : IntegerEndpointWitness 271 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree271.table
  base := (-2920462796876366716064229307903360856681/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-47305428480280521733036813822000000000000)
      constant := (1563471593858349869888451931417023113146552) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 271 interval.damping) (curvature.centralUpper 271 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree271.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 271 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree271.table
  base := (-45632231201193435228234378117269825407/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-2981049762927436655828017382346000000000000)
      constant := (101452190362182464677944714219706618275236480) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 271 interval.damping) (curvature.centralUpper 271 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree271.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 271 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 271 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell003.Kernel271

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel272
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113240727235095828831/25000000000000000000)
  centralHi := (18118516357615332613/4000000000000000000)
  directionLo := (113450238472934555699/25000000000000000000)
  directionHi := (453800953891738222797/100000000000000000000)

def endpointA : IntegerEndpointWitness 272 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree272.table
  base := (-2896179358419239599099677685932782639847/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-47481690511931032433468047424000000000000)
      constant := (1575514251240033331094981452048537738881224) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 272 interval.damping) (curvature.centralUpper 272 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree272.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 272 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree272.table
  base := (-231694348673540076175653816056102404983/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-2992154270921418829955185099272000000000000)
      constant := (102232072622807024974012676441757172769479125) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 272 interval.damping) (curvature.centralUpper 272 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree272.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 272 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 272 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell003.Kernel272

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel273
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113450238472934555699/25000000000000000000)
  centralHi := (453800953891738222797/100000000000000000000)
  directionLo := (227318727027916165559/50000000000000000000)
  directionHi := (454637454055832331119/100000000000000000000)

def endpointA : IntegerEndpointWitness 273 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree273.table
  base := (-1435832958814028837899967112188874077357/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-47657952543581543133899281026000000000000)
      constant := (1587602814148301858427300315797228014762288) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 273 interval.damping) (curvature.centralUpper 273 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree273.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 273 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree273.table
  base := (-5743331835256134971927076785167934166327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (702)
      previous := (243)
      next := (0)
      square := (3084585553883937257546588035000000000000)
      linear := (-429036968416485857726050402314000000000000)
      constant := (14716417575641144325671402854960522304178555) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 273 interval.damping) (curvature.centralUpper 273 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree273.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 273 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 273 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell003.Kernel273

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel274
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (227318727027916165559/50000000000000000000)
  centralHi := (454637454055832331119/100000000000000000000)
  directionLo := (18218896717757048069/4000000000000000000)
  directionHi := (227736208971963100863/50000000000000000000)

def endpointA : IntegerEndpointWitness 274 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree274.table
  base := (-711730619823380349104774983321159714093/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-47834214575232053834330514628000000000000)
      constant := (1599737282544829848283375714582722889149024) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 274 interval.damping) (curvature.centralUpper 274 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree274.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 274 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree274.table
  base := (-1423461239646764936620535256501967291693/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-3014363286909383178209520533124000000000000)
      constant := (103800741579877977390514212962059272054140860) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 274 interval.damping) (curvature.centralUpper 274 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree274.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 274 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 274 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell003.Kernel274

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel275
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18218896717757048069/4000000000000000000)
  centralHi := (227736208971963100863/50000000000000000000)
  directionLo := (11407646349735232531/2500000000000000000)
  directionHi := (456305853989409301241/100000000000000000000)

def endpointA : IntegerEndpointWitness 275 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree275.table
  base := (-1410974524081777476659952164488899487573/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-48010476606882564534761748230000000000000)
      constant := (1611917656391633907124305812274427608198832) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 275 interval.damping) (curvature.centralUpper 275 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree275.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 275 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree275.table
  base := (-5643898096327124555869345201598527572639/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-3025467794903365352336688250050000000000000)
      constant := (104589528271650443466141717639733360744703445) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 275 interval.damping) (curvature.centralUpper 275 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree275.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 275 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 275 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell003.Kernel275

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel276
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11407646349735232531/2500000000000000000)
  centralHi := (456305853989409301241/100000000000000000000)
  directionLo := (28571110659299612873/6250000000000000000)
  directionHi := (457137770548793805969/100000000000000000000)

def endpointA : IntegerEndpointWitness 276 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree276.table
  base := (-1118698251577535464715039987016028398649/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-48186738638533075235192981832000000000000)
      constant := (1624143935651068592427808588423679432027020) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 276 interval.damping) (curvature.centralUpper 276 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree276.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 276 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree276.table
  base := (-2796745628943844990734761897321737139433/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-3036572302897347526463855966976000000000000)
      constant := (105381283102499625164144029569483548801677830) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 276 interval.damping) (curvature.centralUpper 276 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree276.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 276 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 276 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell003.Kernel276

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel277
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28571110659299612873/6250000000000000000)
  centralHi := (457137770548793805969/100000000000000000000)
  directionLo := (91593635180538431753/20000000000000000000)
  directionHi := (228984087951346079383/50000000000000000000)

def endpointA : IntegerEndpointWitness 277 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree277.table
  base := (-27713122262983328594646931785813458497/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-48363000670183585935624215434000000000000)
      constant := (1636416120285822221492743992393599233202400) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 277 interval.damping) (curvature.centralUpper 277 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree277.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 277 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree277.table
  base := (-554262445259667665605358783316957236331/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-3047676810891329700591023683902000000000000)
      constant := (106176006070140181929492275549443254770989050) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 277 interval.damping) (curvature.centralUpper 277 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree277.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 277 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 277 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell003.Kernel277

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel278
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (91593635180538431753/20000000000000000000)
  centralHi := (228984087951346079383/50000000000000000000)
  directionLo := (229398539128389350873/50000000000000000000)
  directionHi := (458797078256778701747/100000000000000000000)

def endpointA : IntegerEndpointWitness 278 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree278.table
  base := (-274564884484979348883836363241751807561/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-48539262701834096636055449036000000000000)
      constant := (1648734210258912746779214586821659855395120) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 278 interval.damping) (curvature.centralUpper 278 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree278.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 278 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree278.table
  base := (-2745648844849798213925960258536369252711/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-3058781318885311874718191400828000000000000)
      constant := (106973697172306963359370011695637979066171610) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 278 interval.damping) (curvature.centralUpper 278 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree278.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 278 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 278 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell003.Kernel278

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel279
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229398539128389350873/50000000000000000000)
  centralHi := (458797078256778701747/100000000000000000000)
  directionLo := (229812242871367850381/50000000000000000000)
  directionHi := (459624485742735700763/100000000000000000000)

def endpointA : IntegerEndpointWitness 279 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree279.table
  base := (-5439510978360559046861557319889567363961/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-48715524733484607336486682638000000000000)
      constant := (1661098205533683696499043033060691730544156) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 279 interval.damping) (curvature.centralUpper 279 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree279.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 279 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree279.table
  base := (-543951097836056721215230043849921769693/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-3069885826879294048845359117754000000000000)
      constant := (107774356406754760564531732252991891664252150) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 279 interval.damping) (curvature.centralUpper 279 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree279.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 279 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 279 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell003.Kernel279

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel280
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229812242871367850381/50000000000000000000)
  centralHi := (459624485742735700763/100000000000000000000)
  directionLo := (23022520320959203507/5000000000000000000)
  directionHi := (460450406419184070141/100000000000000000000)

def endpointA : IntegerEndpointWitness 280 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree280.table
  base := (-5387264327663304789447060470630252358581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-48891786765135118036917916240000000000000)
      constant := (1673508106073800179200376595317478990565676) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 280 interval.damping) (curvature.centralUpper 280 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree280.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 280 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree280.table
  base := (-538726432766331184447218069910440986153/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (702)
      previous := (243)
      next := (0)
      square := (3084585553883937257546588035000000000000)
      linear := (-440141476410468031853218119240000000000000)
      constant := (15511140538751151635753665887371345654846450) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 280 interval.damping) (curvature.centralUpper 280 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree280.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 280 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 280 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell003.Kernel280

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel281
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23022520320959203507/5000000000000000000)
  centralHi := (460450406419184070141/100000000000000000000)
  directionLo := (57659356034074887381/12500000000000000000)
  directionHi := (461274848272599099049/100000000000000000000)

def endpointA : IntegerEndpointWitness 281 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree281.table
  base := (-533455774661213514652044202498083137519/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-49068048796785628737349149842000000000000)
      constant := (1685963911843244951118866452360326674499240) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 281 interval.damping) (curvature.centralUpper 281 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree281.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 281 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree281.table
  base := (-5334557746612141242179000261315040490839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-3092094842867258397099694551606000000000000)
      constant := (109384579263610809841846776025666015079744445) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 281 interval.damping) (curvature.centralUpper 281 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree281.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 281 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 281 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell003.Kernel281

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel282
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57659356034074887381/12500000000000000000)
  centralHi := (461274848272599099049/100000000000000000000)
  directionLo := (462097819218211473823/100000000000000000000)
  directionHi := (14440556850569108557/3125000000000000000)

def endpointA : IntegerEndpointWitness 282 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree282.table
  base := (-528139124413291690785500446176049186943/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-49244310828436139437780383444000000000000)
      constant := (1698465622806314545095419394273958032522280) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 282 interval.damping) (curvature.centralUpper 282 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree282.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 282 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree282.table
  base := (-5281391244132922174546703248605067531509/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-3103199350861240571226862268532000000000000)
      constant := (110194142881626168380772960384940558454780295) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 282 interval.damping) (curvature.centralUpper 282 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree282.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 282 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 282 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell003.Kernel282

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel283
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (462097819218211473823/100000000000000000000)
  centralHi := (14440556850569108557/3125000000000000000)
  directionLo := (462919327100893883819/100000000000000000000)
  directionHi := (23145966355044694191/5000000000000000000)

def endpointA : IntegerEndpointWitness 283 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree283.table
  base := (-2613882414537012692026985373060982902557/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-49420572860086650138211617046000000000000)
      constant := (1711013238927615459887622529197762136779544) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 283 interval.damping) (curvature.centralUpper 283 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree283.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 283 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree283.table
  base := (-2613882414537014967231281601396133656971/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-3114303858855222745354029985458000000000000)
      constant := (111006674623136285120296832271677694508084210) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 283 interval.damping) (curvature.centralUpper 283 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree283.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 283 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 283 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell003.Kernel283

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel284
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (462919327100893883819/100000000000000000000)
  centralHi := (23145966355044694191/5000000000000000000)
  directionLo := (92747875939206698339/20000000000000000000)
  directionHi := (28983711231002093231/6250000000000000000)

def endpointA : IntegerEndpointWitness 284 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree284.table
  base := (-1293419627551820566736029191317506930811/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-49596834891737160838642850648000000000000)
      constant := (1723606760172060408728168753582919889107024) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 284 interval.damping) (curvature.centralUpper 284 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree284.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 284 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree284.table
  base := (-5173678510207286198443082550666919710567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-3125408366849204919481197702384000000000000)
      constant := (111822174485992063749671848591313804670911085) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 284 interval.damping) (curvature.centralUpper 284 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree284.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 284 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 284 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell003.Kernel284

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel285
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (92747875939206698339/20000000000000000000)
  centralHi := (28983711231002093231/6250000000000000000)
  directionLo := (3716463877683124341/800000000000000000)
  directionHi := (232278992355195271313/50000000000000000000)

def endpointA : IntegerEndpointWitness 285 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree285.table
  base := (-5119132296228878958471493841620035428769/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-49773096923387671539074084250000000000000)
      constant := (1736246186504864626009273862139769858284924) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 285 interval.damping) (curvature.centralUpper 285 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree285.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 285 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree285.table
  base := (-2559566148114441177601607651264408039997/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-3136512874843187093608365419310000000000000)
      constant := (112640642468062937378662845611325440060401470) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 285 interval.damping) (curvature.centralUpper 285 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree285.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 285 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 285 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell003.Kernel285

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel286
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3716463877683124341/800000000000000000)
  centralHi := (232278992355195271313/50000000000000000000)
  directionLo := (465375149782943380639/100000000000000000000)
  directionHi := (2908594686143396129/625000000000000000)

def endpointA : IntegerEndpointWitness 286 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree286.table
  base := (-126603154894007141052661514230902873229/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-49949358955038182239505317852000000000000)
      constant := (1748931517891542230997056420492055540283360) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 286 interval.damping) (curvature.centralUpper 286 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree286.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 286 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree286.table
  base := (-1012825239152057715355837479017810719199/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-3147617382837169267735533136236000000000000)
      constant := (113462078567236645815120947977218381868981225) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 286 interval.damping) (curvature.centralUpper 286 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree286.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 286 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 286 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell003.Kernel286

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel287
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (465375149782943380639/100000000000000000000)
  centralHi := (2908594686143396129/625000000000000000)
  directionLo := (116547720621430033543/25000000000000000000)
  directionHi := (466190882485720134173/100000000000000000000)

def endpointA : IntegerEndpointWitness 287 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree287.table
  base := (-2504330108674573182354462578234480423999/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-50125620986688692939936551454000000000000)
      constant := (1761662754297902647504076795806374156608008) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 287 interval.damping) (curvature.centralUpper 287 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree287.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 287 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree287.table
  base := (-5008660217349148900149811838848960917353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (702)
      previous := (243)
      next := (0)
      square := (3084585553883937257546588035000000000000)
      linear := (-451245984404450205980385836166000000000000)
      constant := (16326640397345573752855192357345686367892645) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 287 interval.damping) (curvature.centralUpper 287 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree287.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 287 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 287 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell003.Kernel287

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel288
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (116547720621430033543/25000000000000000000)
  centralHi := (466190882485720134173/100000000000000000000)
  directionLo := (467005190324617326979/100000000000000000000)
  directionHi := (23350259516230866349/5000000000000000000)

def endpointA : IntegerEndpointWitness 288 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree288.table
  base := (-2476367184735080195419898093791128131457/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-50301883018339203640367785056000000000000)
      constant := (1774439895690047078472091353745670974948344) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 288 interval.damping) (curvature.centralUpper 288 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree288.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 288 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree288.table
  base := (-309545898091885161333569125235597370349/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-3169826398825133615989868570088000000000000)
      constant := (115113855108533747425533646928289258308231920) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 288 interval.damping) (curvature.centralUpper 288 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree288.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 288 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 288 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell003.Kernel288

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel289
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (467005190324617326979/100000000000000000000)
  centralHi := (23350259516230866349/5000000000000000000)
  directionLo := (233909040370102832371/50000000000000000000)
  directionHi := (467818080740205664743/100000000000000000000)

def endpointA : IntegerEndpointWitness 289 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree289.table
  base := (-2448174330262975042886419887226452284363/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-50478145049989714340799018658000000000000)
      constant := (1787262942034365034440005029862438381725096) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 289 interval.damping) (curvature.centralUpper 289 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree289.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 289 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree289.table
  base := (-612043582565743997279490217905978944689/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-3180930906819115790117036287014000000000000)
      constant := (115944195546522196804078610553744481268409560) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 289 interval.damping) (curvature.centralUpper 289 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree289.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 289 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 289 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell003.Kernel289

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel290
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (233909040370102832371/50000000000000000000)
  centralHi := (467818080740205664743/100000000000000000000)
  directionLo := (468629561108523242083/100000000000000000000)
  directionHi := (117157390277130810521/25000000000000000000)

def endpointA : IntegerEndpointWitness 290 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree290.table
  base := (-4839503098847915577792268471186548355703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-50654407081640225041230252260000000000000)
      constant := (1800131893297530914894680973940253806577188) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 290 interval.damping) (curvature.centralUpper 290 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree290.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 290 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree290.table
  base := (-4839503098847917212754034531632688543737/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-3192035414813097964244204003940000000000000)
      constant := (116777504093343171375753832386569991306784435) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 290 interval.damping) (curvature.centralUpper 290 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree290.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 290 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 290 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell003.Kernel290

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel291
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (468629561108523242083/100000000000000000000)
  centralHi := (117157390277130810521/25000000000000000000)
  directionLo := (469439638741856409171/100000000000000000000)
  directionHi := (117359909685464102293/25000000000000000000)

def endpointA : IntegerEndpointWitness 291 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree291.table
  base := (-4782197692697076444907424167780684041709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-50830669113290735741661485862000000000000)
      constant := (1813046749446500641524081818419127263833164) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 291 interval.damping) (curvature.centralUpper 291 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree291.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 291 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree291.table
  base := (-239109884634853892869535017979964705679/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-3203139922807080138371371720866000000000000)
      constant := (117613780746972721345296994709050372942172900) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 291 interval.damping) (curvature.centralUpper 291 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree291.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 291 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 291 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell003.Kernel291

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel292
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (469439638741856409171/100000000000000000000)
  centralHi := (117359909685464102293/25000000000000000000)
  directionLo := (470248320889508531773/100000000000000000000)
  directionHi := (235124160444754265887/50000000000000000000)

def endpointA : IntegerEndpointWitness 292 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree292.table
  base := (-4724432450264900665744692756258727880941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-51006931144941246442092719464000000000000)
      constant := (1826007510448508342413702019730965088476236) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 292 interval.damping) (curvature.centralUpper 292 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree292.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 292 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree292.table
  base := (-4724432450264901886010919231380810939323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-3214244430801062312498539437792000000000000)
      constant := (118453025505403937059111172520148501319865865) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 292 interval.damping) (curvature.centralUpper 292 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree292.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 292 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 292 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell003.Kernel292

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel293
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (470248320889508531773/100000000000000000000)
  centralHi := (235124160444754265887/50000000000000000000)
  directionLo := (235527807369278436683/50000000000000000000)
  directionHi := (471055614738556873367/100000000000000000000)

def endpointA : IntegerEndpointWitness 293 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree293.table
  base := (-291637961229632566823713427917065473663/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-51183193176591757142523953066000000000000)
      constant := (1839014176271063086248040215435557809685568) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 293 interval.damping) (curvature.centralUpper 293 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree293.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 293 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree293.table
  base := (-4666207379674122123375663547989840866043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-3225348938795044486625707154718000000000000)
      constant := (119295238366646748975129927581616288987819465) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 293 interval.damping) (curvature.centralUpper 293 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree293.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 293 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 293 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell003.Kernel293

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel294
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (235527807369278436683/50000000000000000000)
  centralHi := (471055614738556873367/100000000000000000000)
  directionLo := (29491345463412363929/6250000000000000000)
  directionHi := (94372305482919564573/20000000000000000000)

def endpointA : IntegerEndpointWitness 294 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree294.table
  base := (-575940311122442439020007054180622812867/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-51359455208242267842955186668000000000000)
      constant := (1852066746881945665599302541555220069988256) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 294 interval.damping) (curvature.centralUpper 294 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree294.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 294 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree294.table
  base := (-1151880622244885105719542251825865602051/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (702)
      previous := (243)
      next := (0)
      square := (3084585553883937257546588035000000000000)
      linear := (-462350492398432380107553553092000000000000)
      constant := (17162917046961104377038845306781978815712860) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 294 interval.damping) (curvature.centralUpper 294 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree294.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 294 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 294 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell003.Kernel294

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel295
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29491345463412363929/6250000000000000000)
  centralHi := (94372305482919564573/20000000000000000000)
  directionLo := (94533213196496137303/20000000000000000000)
  directionHi := (118166516495620171629/25000000000000000000)

def endpointA : IntegerEndpointWitness 295 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree295.table
  base := (-22741888930844095051363284358613868541/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-51535717239892778543386420270000000000000)
      constant := (1865165222249205428405144840669358905167200) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 295 interval.damping) (curvature.centralUpper 295 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree295.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 295 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree295.table
  base := (-4548377786168819797032432808750884287361/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-3247557954783008834880042588570000000000000)
      constant := (120988568389689904613471211903861033349596555) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 295 interval.damping) (curvature.centralUpper 295 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree295.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 295 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 295 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell003.Kernel295

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel296
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94533213196496137303/20000000000000000000)
  centralHi := (118166516495620171629/25000000000000000000)
  directionLo := (473469237447030257763/100000000000000000000)
  directionHi := (118367309361757564441/25000000000000000000)

def endpointA : IntegerEndpointWitness 296 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree296.table
  base := (-2244386639581632020338298526071382203439/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-51711979271543289243817653872000000000000)
      constant := (1878309602341157156756929589215428942372488) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 296 interval.damping) (curvature.centralUpper 296 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree296.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 296 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree296.table
  base := (-4488773279163264720343343382239764307379/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-3258662462776991009007210305496000000000000)
      constant := (121839685547592551301474114185450457744692145) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 296 interval.damping) (curvature.centralUpper 296 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree296.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 296 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 296 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell003.Kernel296

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel297
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (473469237447030257763/100000000000000000000)
  centralHi := (118367309361757564441/25000000000000000000)
  directionLo := (474271048753758374089/100000000000000000000)
  directionHi := (47427104875375837409/10000000000000000000)

def endpointA : IntegerEndpointWitness 297 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree297.table
  base := (-553588621977323654052313692587248839803/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-51888241303193799944248887474000000000000)
      constant := (1891499887126377992138470256929458037126304) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 297 interval.damping) (curvature.centralUpper 297 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree297.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 297 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree297.table
  base := (-2214354487909294909781932118225157259239/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-3269766970770973183134378022422000000000000)
      constant := (122693770800511020619726147932615472942972890) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 297 interval.damping) (curvature.centralUpper 297 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree297.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 297 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 297 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell003.Kernel297

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel298
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (474271048753758374089/100000000000000000000)
  centralHi := (47427104875375837409/10000000000000000000)
  directionLo := (47507150678956466531/10000000000000000000)
  directionHi := (475071506789564665311/100000000000000000000)

def endpointA : IntegerEndpointWitness 298 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree298.table
  base := (-1092046220981419163617586850069814460053/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-52064503334844310644680121076000000000000)
      constant := (1904736076573704406273879031559882968639152) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 298 interval.damping) (curvature.centralUpper 298 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree298.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 298 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree298.table
  base := (-4368184883925677161684079221954552107629/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-3280871478764955357261545739348000000000000)
      constant := (123550824146536546461814742601965934733630895) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 298 interval.damping) (curvature.centralUpper 298 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree298.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 298 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 298 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell003.Kernel298

namespace ForestUnimodality.Stage170KernelData.Cell003.Kernel299
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47507150678956466531/10000000000000000000)
  centralHi := (475071506789564665311/100000000000000000000)
  directionLo := (475870618383426693333/100000000000000000000)
  directionHi := (237935309191713346667/50000000000000000000)

def endpointA : IntegerEndpointWitness 299 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree299.table
  base := (-2153600505605660953682736425485381023563/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (81)
      previous := (27)
      next := (0)
      square := (352524063301021400862467204000000000000)
      linear := (-52240765366494821345111354678000000000000)
      constant := (1918018170652229216761022464226366951811496) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 299 interval.damping) (curvature.centralUpper 299 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree299.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 299 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree299.table
  base := (-2153600505605661172762457488832807325609/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4914)
      previous := (1701)
      next := (0)
      square := (21592098877187560802826116245000000000000)
      linear := (-3291975986758937531388713456274000000000000)
      constant := (124410845583776063906028771166968124410451590) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 299 interval.damping) (curvature.centralUpper 299 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree299.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 299 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 299 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell003.Kernel299
