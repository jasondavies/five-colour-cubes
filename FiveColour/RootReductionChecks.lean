module
public import FiveColour.RootContainment
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace FiveColour.Physical

/-- Every nontrivial change is one of the 49 containment witnesses below.
Original case numbers and archive headers remain unchanged. -/
def rootRepresentative (r : Fin 357) : Fin 357 :=
  if r = 39 then 32 else
  if r = 44 then 41 else
  if r = 53 then 47 else
  if r = 56 then 45 else
  if r = 63 then 58 else
  if r = 66 then 60 else
  if r = 70 then 68 else
  if r = 86 then 77 else
  if r = 91 then 87 else
  if r = 95 then 92 else
  if r = 96 then 97 else
  if r = 120 then 113 else
  if r = 125 then 122 else
  if r = 134 then 128 else
  if r = 137 then 126 else
  if r = 144 then 139 else
  if r = 147 then 141 else
  if r = 151 then 149 else
  if r = 162 then 153 else
  if r = 167 then 163 else
  if r = 171 then 168 else
  if r = 172 then 173 else
  if r = 177 then 174 else
  if r = 186 then 180 else
  if r = 189 then 178 else
  if r = 196 then 191 else
  if r = 199 then 193 else
  if r = 203 then 201 else
  if r = 209 then 205 else
  if r = 213 then 210 else
  if r = 214 then 215 else
  if r = 221 then 216 else
  if r = 224 then 218 else
  if r = 228 then 226 else
  if r = 233 then 230 else
  if r = 234 then 235 else
  if r = 238 then 236 else
  if r = 240 then 241 else
  if r = 293 then 286 else
  if r = 298 then 295 else
  if r = 307 then 301 else
  if r = 310 then 299 else
  if r = 317 then 312 else
  if r = 320 then 314 else
  if r = 324 then 322 else
  if r = 345 then 336 else
  if r = 350 then 346 else
  if r = 354 then 351 else
  if r = 355 then 356 else
  r

def retainedRoots : Finset (Fin 357) :=
  Finset.univ.filter fun r => rootRepresentative r = r

/-- Retained roots whose budget and upper box already contradict total 15. -/
def arithmeticRoots : Finset (Fin 357) :=
  {84, 87, 88, 89, 90, 92, 93, 94, 97, 169, 170, 173, 211, 212, 215, 235, 241, 243, 341, 343, 344, 346, 347, 348, 349, 351, 352, 353, 356}

/-- Only these 279 roots require further exclusion proofs. -/
def replayRoots : Finset (Fin 357) := retainedRoots \ arithmeticRoots

lemma representative_mem (r : Fin 357) : rootRepresentative r ∈ retainedRoots := by
  have h : ∀ s : Fin 357, rootRepresentative s ∈ retainedRoots := by decide +kernel
  exact h r

lemma retainedRoots_card : retainedRoots.card = 308 := by decide +kernel
lemma arithmeticRoots_card : arithmeticRoots.card = 29 := by decide +kernel
lemma arithmeticRoots_subset : arithmeticRoots ⊆ retainedRoots := by decide +kernel
lemma replayRoots_card : replayRoots.card = 279 := by decide +kernel

lemma root_contains_39 : RootContains 32 39 := by decide +kernel
lemma root_contains_44 : RootContains 41 44 := by decide +kernel
lemma root_contains_53 : RootContains 47 53 := by decide +kernel
lemma root_contains_56 : RootContains 45 56 := by decide +kernel
lemma root_contains_63 : RootContains 58 63 := by decide +kernel
lemma root_contains_66 : RootContains 60 66 := by decide +kernel
lemma root_contains_70 : RootContains 68 70 := by decide +kernel
lemma root_contains_86 : RootContains 77 86 := by decide +kernel
lemma root_contains_91 : RootContains 87 91 := by decide +kernel
lemma root_contains_95 : RootContains 92 95 := by decide +kernel
lemma root_contains_96 : RootContains 97 96 := by decide +kernel
lemma root_contains_120 : RootContains 113 120 := by decide +kernel
lemma root_contains_125 : RootContains 122 125 := by decide +kernel
lemma root_contains_134 : RootContains 128 134 := by decide +kernel
lemma root_contains_137 : RootContains 126 137 := by decide +kernel
lemma root_contains_144 : RootContains 139 144 := by decide +kernel
lemma root_contains_147 : RootContains 141 147 := by decide +kernel
lemma root_contains_151 : RootContains 149 151 := by decide +kernel
lemma root_contains_162 : RootContains 153 162 := by decide +kernel
lemma root_contains_167 : RootContains 163 167 := by decide +kernel
lemma root_contains_171 : RootContains 168 171 := by decide +kernel
lemma root_contains_172 : RootContains 173 172 := by decide +kernel
lemma root_contains_177 : RootContains 174 177 := by decide +kernel
lemma root_contains_186 : RootContains 180 186 := by decide +kernel
lemma root_contains_189 : RootContains 178 189 := by decide +kernel
lemma root_contains_196 : RootContains 191 196 := by decide +kernel
lemma root_contains_199 : RootContains 193 199 := by decide +kernel
lemma root_contains_203 : RootContains 201 203 := by decide +kernel
lemma root_contains_209 : RootContains 205 209 := by decide +kernel
lemma root_contains_213 : RootContains 210 213 := by decide +kernel
lemma root_contains_214 : RootContains 215 214 := by decide +kernel
lemma root_contains_221 : RootContains 216 221 := by decide +kernel
lemma root_contains_224 : RootContains 218 224 := by decide +kernel
lemma root_contains_228 : RootContains 226 228 := by decide +kernel
lemma root_contains_233 : RootContains 230 233 := by decide +kernel
lemma root_contains_234 : RootContains 235 234 := by decide +kernel
lemma root_contains_238 : RootContains 236 238 := by decide +kernel
lemma root_contains_240 : RootContains 241 240 := by decide +kernel
lemma root_contains_293 : RootContains 286 293 := by decide +kernel
lemma root_contains_298 : RootContains 295 298 := by decide +kernel
lemma root_contains_307 : RootContains 301 307 := by decide +kernel
lemma root_contains_310 : RootContains 299 310 := by decide +kernel
lemma root_contains_317 : RootContains 312 317 := by decide +kernel
lemma root_contains_320 : RootContains 314 320 := by decide +kernel
lemma root_contains_324 : RootContains 322 324 := by decide +kernel
lemma root_contains_345 : RootContains 336 345 := by decide +kernel
lemma root_contains_350 : RootContains 346 350 := by decide +kernel
lemma root_contains_354 : RootContains 351 354 := by decide +kernel
lemma root_contains_355 : RootContains 356 355 := by decide +kernel

/-- The full box and admissibility transport has a checked witness for every root. -/
theorem representative_contains (r : Fin 357) : RootContains (rootRepresentative r) r := by
  fin_cases r
  · exact RootContains.refl 0
  · exact RootContains.refl 1
  · exact RootContains.refl 2
  · exact RootContains.refl 3
  · exact RootContains.refl 4
  · exact RootContains.refl 5
  · exact RootContains.refl 6
  · exact RootContains.refl 7
  · exact RootContains.refl 8
  · exact RootContains.refl 9
  · exact RootContains.refl 10
  · exact RootContains.refl 11
  · exact RootContains.refl 12
  · exact RootContains.refl 13
  · exact RootContains.refl 14
  · exact RootContains.refl 15
  · exact RootContains.refl 16
  · exact RootContains.refl 17
  · exact RootContains.refl 18
  · exact RootContains.refl 19
  · exact RootContains.refl 20
  · exact RootContains.refl 21
  · exact RootContains.refl 22
  · exact RootContains.refl 23
  · exact RootContains.refl 24
  · exact RootContains.refl 25
  · exact RootContains.refl 26
  · exact RootContains.refl 27
  · exact RootContains.refl 28
  · exact RootContains.refl 29
  · exact RootContains.refl 30
  · exact RootContains.refl 31
  · exact RootContains.refl 32
  · exact RootContains.refl 33
  · exact RootContains.refl 34
  · exact RootContains.refl 35
  · exact RootContains.refl 36
  · exact RootContains.refl 37
  · exact RootContains.refl 38
  · exact root_contains_39
  · exact RootContains.refl 40
  · exact RootContains.refl 41
  · exact RootContains.refl 42
  · exact RootContains.refl 43
  · exact root_contains_44
  · exact RootContains.refl 45
  · exact RootContains.refl 46
  · exact RootContains.refl 47
  · exact RootContains.refl 48
  · exact RootContains.refl 49
  · exact RootContains.refl 50
  · exact RootContains.refl 51
  · exact RootContains.refl 52
  · exact root_contains_53
  · exact RootContains.refl 54
  · exact RootContains.refl 55
  · exact root_contains_56
  · exact RootContains.refl 57
  · exact RootContains.refl 58
  · exact RootContains.refl 59
  · exact RootContains.refl 60
  · exact RootContains.refl 61
  · exact RootContains.refl 62
  · exact root_contains_63
  · exact RootContains.refl 64
  · exact RootContains.refl 65
  · exact root_contains_66
  · exact RootContains.refl 67
  · exact RootContains.refl 68
  · exact RootContains.refl 69
  · exact root_contains_70
  · exact RootContains.refl 71
  · exact RootContains.refl 72
  · exact RootContains.refl 73
  · exact RootContains.refl 74
  · exact RootContains.refl 75
  · exact RootContains.refl 76
  · exact RootContains.refl 77
  · exact RootContains.refl 78
  · exact RootContains.refl 79
  · exact RootContains.refl 80
  · exact RootContains.refl 81
  · exact RootContains.refl 82
  · exact RootContains.refl 83
  · exact RootContains.refl 84
  · exact RootContains.refl 85
  · exact root_contains_86
  · exact RootContains.refl 87
  · exact RootContains.refl 88
  · exact RootContains.refl 89
  · exact RootContains.refl 90
  · exact root_contains_91
  · exact RootContains.refl 92
  · exact RootContains.refl 93
  · exact RootContains.refl 94
  · exact root_contains_95
  · exact root_contains_96
  · exact RootContains.refl 97
  · exact RootContains.refl 98
  · exact RootContains.refl 99
  · exact RootContains.refl 100
  · exact RootContains.refl 101
  · exact RootContains.refl 102
  · exact RootContains.refl 103
  · exact RootContains.refl 104
  · exact RootContains.refl 105
  · exact RootContains.refl 106
  · exact RootContains.refl 107
  · exact RootContains.refl 108
  · exact RootContains.refl 109
  · exact RootContains.refl 110
  · exact RootContains.refl 111
  · exact RootContains.refl 112
  · exact RootContains.refl 113
  · exact RootContains.refl 114
  · exact RootContains.refl 115
  · exact RootContains.refl 116
  · exact RootContains.refl 117
  · exact RootContains.refl 118
  · exact RootContains.refl 119
  · exact root_contains_120
  · exact RootContains.refl 121
  · exact RootContains.refl 122
  · exact RootContains.refl 123
  · exact RootContains.refl 124
  · exact root_contains_125
  · exact RootContains.refl 126
  · exact RootContains.refl 127
  · exact RootContains.refl 128
  · exact RootContains.refl 129
  · exact RootContains.refl 130
  · exact RootContains.refl 131
  · exact RootContains.refl 132
  · exact RootContains.refl 133
  · exact root_contains_134
  · exact RootContains.refl 135
  · exact RootContains.refl 136
  · exact root_contains_137
  · exact RootContains.refl 138
  · exact RootContains.refl 139
  · exact RootContains.refl 140
  · exact RootContains.refl 141
  · exact RootContains.refl 142
  · exact RootContains.refl 143
  · exact root_contains_144
  · exact RootContains.refl 145
  · exact RootContains.refl 146
  · exact root_contains_147
  · exact RootContains.refl 148
  · exact RootContains.refl 149
  · exact RootContains.refl 150
  · exact root_contains_151
  · exact RootContains.refl 152
  · exact RootContains.refl 153
  · exact RootContains.refl 154
  · exact RootContains.refl 155
  · exact RootContains.refl 156
  · exact RootContains.refl 157
  · exact RootContains.refl 158
  · exact RootContains.refl 159
  · exact RootContains.refl 160
  · exact RootContains.refl 161
  · exact root_contains_162
  · exact RootContains.refl 163
  · exact RootContains.refl 164
  · exact RootContains.refl 165
  · exact RootContains.refl 166
  · exact root_contains_167
  · exact RootContains.refl 168
  · exact RootContains.refl 169
  · exact RootContains.refl 170
  · exact root_contains_171
  · exact root_contains_172
  · exact RootContains.refl 173
  · exact RootContains.refl 174
  · exact RootContains.refl 175
  · exact RootContains.refl 176
  · exact root_contains_177
  · exact RootContains.refl 178
  · exact RootContains.refl 179
  · exact RootContains.refl 180
  · exact RootContains.refl 181
  · exact RootContains.refl 182
  · exact RootContains.refl 183
  · exact RootContains.refl 184
  · exact RootContains.refl 185
  · exact root_contains_186
  · exact RootContains.refl 187
  · exact RootContains.refl 188
  · exact root_contains_189
  · exact RootContains.refl 190
  · exact RootContains.refl 191
  · exact RootContains.refl 192
  · exact RootContains.refl 193
  · exact RootContains.refl 194
  · exact RootContains.refl 195
  · exact root_contains_196
  · exact RootContains.refl 197
  · exact RootContains.refl 198
  · exact root_contains_199
  · exact RootContains.refl 200
  · exact RootContains.refl 201
  · exact RootContains.refl 202
  · exact root_contains_203
  · exact RootContains.refl 204
  · exact RootContains.refl 205
  · exact RootContains.refl 206
  · exact RootContains.refl 207
  · exact RootContains.refl 208
  · exact root_contains_209
  · exact RootContains.refl 210
  · exact RootContains.refl 211
  · exact RootContains.refl 212
  · exact root_contains_213
  · exact root_contains_214
  · exact RootContains.refl 215
  · exact RootContains.refl 216
  · exact RootContains.refl 217
  · exact RootContains.refl 218
  · exact RootContains.refl 219
  · exact RootContains.refl 220
  · exact root_contains_221
  · exact RootContains.refl 222
  · exact RootContains.refl 223
  · exact root_contains_224
  · exact RootContains.refl 225
  · exact RootContains.refl 226
  · exact RootContains.refl 227
  · exact root_contains_228
  · exact RootContains.refl 229
  · exact RootContains.refl 230
  · exact RootContains.refl 231
  · exact RootContains.refl 232
  · exact root_contains_233
  · exact root_contains_234
  · exact RootContains.refl 235
  · exact RootContains.refl 236
  · exact RootContains.refl 237
  · exact root_contains_238
  · exact RootContains.refl 239
  · exact root_contains_240
  · exact RootContains.refl 241
  · exact RootContains.refl 242
  · exact RootContains.refl 243
  · exact RootContains.refl 244
  · exact RootContains.refl 245
  · exact RootContains.refl 246
  · exact RootContains.refl 247
  · exact RootContains.refl 248
  · exact RootContains.refl 249
  · exact RootContains.refl 250
  · exact RootContains.refl 251
  · exact RootContains.refl 252
  · exact RootContains.refl 253
  · exact RootContains.refl 254
  · exact RootContains.refl 255
  · exact RootContains.refl 256
  · exact RootContains.refl 257
  · exact RootContains.refl 258
  · exact RootContains.refl 259
  · exact RootContains.refl 260
  · exact RootContains.refl 261
  · exact RootContains.refl 262
  · exact RootContains.refl 263
  · exact RootContains.refl 264
  · exact RootContains.refl 265
  · exact RootContains.refl 266
  · exact RootContains.refl 267
  · exact RootContains.refl 268
  · exact RootContains.refl 269
  · exact RootContains.refl 270
  · exact RootContains.refl 271
  · exact RootContains.refl 272
  · exact RootContains.refl 273
  · exact RootContains.refl 274
  · exact RootContains.refl 275
  · exact RootContains.refl 276
  · exact RootContains.refl 277
  · exact RootContains.refl 278
  · exact RootContains.refl 279
  · exact RootContains.refl 280
  · exact RootContains.refl 281
  · exact RootContains.refl 282
  · exact RootContains.refl 283
  · exact RootContains.refl 284
  · exact RootContains.refl 285
  · exact RootContains.refl 286
  · exact RootContains.refl 287
  · exact RootContains.refl 288
  · exact RootContains.refl 289
  · exact RootContains.refl 290
  · exact RootContains.refl 291
  · exact RootContains.refl 292
  · exact root_contains_293
  · exact RootContains.refl 294
  · exact RootContains.refl 295
  · exact RootContains.refl 296
  · exact RootContains.refl 297
  · exact root_contains_298
  · exact RootContains.refl 299
  · exact RootContains.refl 300
  · exact RootContains.refl 301
  · exact RootContains.refl 302
  · exact RootContains.refl 303
  · exact RootContains.refl 304
  · exact RootContains.refl 305
  · exact RootContains.refl 306
  · exact root_contains_307
  · exact RootContains.refl 308
  · exact RootContains.refl 309
  · exact root_contains_310
  · exact RootContains.refl 311
  · exact RootContains.refl 312
  · exact RootContains.refl 313
  · exact RootContains.refl 314
  · exact RootContains.refl 315
  · exact RootContains.refl 316
  · exact root_contains_317
  · exact RootContains.refl 318
  · exact RootContains.refl 319
  · exact root_contains_320
  · exact RootContains.refl 321
  · exact RootContains.refl 322
  · exact RootContains.refl 323
  · exact root_contains_324
  · exact RootContains.refl 325
  · exact RootContains.refl 326
  · exact RootContains.refl 327
  · exact RootContains.refl 328
  · exact RootContains.refl 329
  · exact RootContains.refl 330
  · exact RootContains.refl 331
  · exact RootContains.refl 332
  · exact RootContains.refl 333
  · exact RootContains.refl 334
  · exact RootContains.refl 335
  · exact RootContains.refl 336
  · exact RootContains.refl 337
  · exact RootContains.refl 338
  · exact RootContains.refl 339
  · exact RootContains.refl 340
  · exact RootContains.refl 341
  · exact RootContains.refl 342
  · exact RootContains.refl 343
  · exact RootContains.refl 344
  · exact root_contains_345
  · exact RootContains.refl 346
  · exact RootContains.refl 347
  · exact RootContains.refl 348
  · exact RootContains.refl 349
  · exact root_contains_350
  · exact RootContains.refl 351
  · exact RootContains.refl 352
  · exact RootContains.refl 353
  · exact root_contains_354
  · exact root_contains_355
  · exact RootContains.refl 356

lemma impossible_budget_84 :
    ¬ (⟨rootBad (rootCapacity 84), (rootCapacity 84).budget⟩ : Certificate.Cut 75).Possible
      (rootBox (rootCapacity 84)) 15 := by decide +kernel
lemma impossible_budget_87 :
    ¬ (⟨rootBad (rootCapacity 87), (rootCapacity 87).budget⟩ : Certificate.Cut 75).Possible
      (rootBox (rootCapacity 87)) 15 := by decide +kernel
lemma impossible_budget_88 :
    ¬ (⟨rootBad (rootCapacity 88), (rootCapacity 88).budget⟩ : Certificate.Cut 75).Possible
      (rootBox (rootCapacity 88)) 15 := by decide +kernel
lemma impossible_budget_89 :
    ¬ (⟨rootBad (rootCapacity 89), (rootCapacity 89).budget⟩ : Certificate.Cut 75).Possible
      (rootBox (rootCapacity 89)) 15 := by decide +kernel
lemma impossible_budget_90 :
    ¬ (⟨rootBad (rootCapacity 90), (rootCapacity 90).budget⟩ : Certificate.Cut 75).Possible
      (rootBox (rootCapacity 90)) 15 := by decide +kernel
lemma impossible_budget_92 :
    ¬ (⟨rootBad (rootCapacity 92), (rootCapacity 92).budget⟩ : Certificate.Cut 75).Possible
      (rootBox (rootCapacity 92)) 15 := by decide +kernel
lemma impossible_budget_93 :
    ¬ (⟨rootBad (rootCapacity 93), (rootCapacity 93).budget⟩ : Certificate.Cut 75).Possible
      (rootBox (rootCapacity 93)) 15 := by decide +kernel
lemma impossible_budget_94 :
    ¬ (⟨rootBad (rootCapacity 94), (rootCapacity 94).budget⟩ : Certificate.Cut 75).Possible
      (rootBox (rootCapacity 94)) 15 := by decide +kernel
lemma impossible_budget_97 :
    ¬ (⟨rootBad (rootCapacity 97), (rootCapacity 97).budget⟩ : Certificate.Cut 75).Possible
      (rootBox (rootCapacity 97)) 15 := by decide +kernel
lemma impossible_budget_169 :
    ¬ (⟨rootBad (rootCapacity 169), (rootCapacity 169).budget⟩ : Certificate.Cut 75).Possible
      (rootBox (rootCapacity 169)) 15 := by decide +kernel
lemma impossible_budget_170 :
    ¬ (⟨rootBad (rootCapacity 170), (rootCapacity 170).budget⟩ : Certificate.Cut 75).Possible
      (rootBox (rootCapacity 170)) 15 := by decide +kernel
lemma impossible_budget_173 :
    ¬ (⟨rootBad (rootCapacity 173), (rootCapacity 173).budget⟩ : Certificate.Cut 75).Possible
      (rootBox (rootCapacity 173)) 15 := by decide +kernel
lemma impossible_budget_211 :
    ¬ (⟨rootBad (rootCapacity 211), (rootCapacity 211).budget⟩ : Certificate.Cut 75).Possible
      (rootBox (rootCapacity 211)) 15 := by decide +kernel
lemma impossible_budget_212 :
    ¬ (⟨rootBad (rootCapacity 212), (rootCapacity 212).budget⟩ : Certificate.Cut 75).Possible
      (rootBox (rootCapacity 212)) 15 := by decide +kernel
lemma impossible_budget_215 :
    ¬ (⟨rootBad (rootCapacity 215), (rootCapacity 215).budget⟩ : Certificate.Cut 75).Possible
      (rootBox (rootCapacity 215)) 15 := by decide +kernel
lemma impossible_budget_235 :
    ¬ (⟨rootBad (rootCapacity 235), (rootCapacity 235).budget⟩ : Certificate.Cut 75).Possible
      (rootBox (rootCapacity 235)) 15 := by decide +kernel
lemma impossible_budget_241 :
    ¬ (⟨rootBad (rootCapacity 241), (rootCapacity 241).budget⟩ : Certificate.Cut 75).Possible
      (rootBox (rootCapacity 241)) 15 := by decide +kernel
lemma impossible_budget_243 :
    ¬ (⟨rootBad (rootCapacity 243), (rootCapacity 243).budget⟩ : Certificate.Cut 75).Possible
      (rootBox (rootCapacity 243)) 15 := by decide +kernel
lemma impossible_budget_341 :
    ¬ (⟨rootBad (rootCapacity 341), (rootCapacity 341).budget⟩ : Certificate.Cut 75).Possible
      (rootBox (rootCapacity 341)) 15 := by decide +kernel
lemma impossible_budget_343 :
    ¬ (⟨rootBad (rootCapacity 343), (rootCapacity 343).budget⟩ : Certificate.Cut 75).Possible
      (rootBox (rootCapacity 343)) 15 := by decide +kernel
lemma impossible_budget_344 :
    ¬ (⟨rootBad (rootCapacity 344), (rootCapacity 344).budget⟩ : Certificate.Cut 75).Possible
      (rootBox (rootCapacity 344)) 15 := by decide +kernel
lemma impossible_budget_346 :
    ¬ (⟨rootBad (rootCapacity 346), (rootCapacity 346).budget⟩ : Certificate.Cut 75).Possible
      (rootBox (rootCapacity 346)) 15 := by decide +kernel
lemma impossible_budget_347 :
    ¬ (⟨rootBad (rootCapacity 347), (rootCapacity 347).budget⟩ : Certificate.Cut 75).Possible
      (rootBox (rootCapacity 347)) 15 := by decide +kernel
lemma impossible_budget_348 :
    ¬ (⟨rootBad (rootCapacity 348), (rootCapacity 348).budget⟩ : Certificate.Cut 75).Possible
      (rootBox (rootCapacity 348)) 15 := by decide +kernel
lemma impossible_budget_349 :
    ¬ (⟨rootBad (rootCapacity 349), (rootCapacity 349).budget⟩ : Certificate.Cut 75).Possible
      (rootBox (rootCapacity 349)) 15 := by decide +kernel
lemma impossible_budget_351 :
    ¬ (⟨rootBad (rootCapacity 351), (rootCapacity 351).budget⟩ : Certificate.Cut 75).Possible
      (rootBox (rootCapacity 351)) 15 := by decide +kernel
lemma impossible_budget_352 :
    ¬ (⟨rootBad (rootCapacity 352), (rootCapacity 352).budget⟩ : Certificate.Cut 75).Possible
      (rootBox (rootCapacity 352)) 15 := by decide +kernel
lemma impossible_budget_353 :
    ¬ (⟨rootBad (rootCapacity 353), (rootCapacity 353).budget⟩ : Certificate.Cut 75).Possible
      (rootBox (rootCapacity 353)) 15 := by decide +kernel
lemma impossible_budget_356 :
    ¬ (⟨rootBad (rootCapacity 356), (rootCapacity 356).budget⟩ : Certificate.Cut 75).Possible
      (rootBox (rootCapacity 356)) 15 := by decide +kernel

/-- These 29 exclusions use only the initial budget capacity bound, not a certificate. -/
theorem arithmetic_root_excluded (r : Fin 357) (hr : r ∈ arithmeticRoots) :
    ∀ x, (rootBox (rootCapacity r)).Contains x → ¬ (rootProblem r).Admissible x := by
  simp only [arithmeticRoots, Finset.mem_insert, Finset.mem_singleton] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact root_excluded_of_impossible_budget 84 impossible_budget_84
  · exact root_excluded_of_impossible_budget 87 impossible_budget_87
  · exact root_excluded_of_impossible_budget 88 impossible_budget_88
  · exact root_excluded_of_impossible_budget 89 impossible_budget_89
  · exact root_excluded_of_impossible_budget 90 impossible_budget_90
  · exact root_excluded_of_impossible_budget 92 impossible_budget_92
  · exact root_excluded_of_impossible_budget 93 impossible_budget_93
  · exact root_excluded_of_impossible_budget 94 impossible_budget_94
  · exact root_excluded_of_impossible_budget 97 impossible_budget_97
  · exact root_excluded_of_impossible_budget 169 impossible_budget_169
  · exact root_excluded_of_impossible_budget 170 impossible_budget_170
  · exact root_excluded_of_impossible_budget 173 impossible_budget_173
  · exact root_excluded_of_impossible_budget 211 impossible_budget_211
  · exact root_excluded_of_impossible_budget 212 impossible_budget_212
  · exact root_excluded_of_impossible_budget 215 impossible_budget_215
  · exact root_excluded_of_impossible_budget 235 impossible_budget_235
  · exact root_excluded_of_impossible_budget 241 impossible_budget_241
  · exact root_excluded_of_impossible_budget 243 impossible_budget_243
  · exact root_excluded_of_impossible_budget 341 impossible_budget_341
  · exact root_excluded_of_impossible_budget 343 impossible_budget_343
  · exact root_excluded_of_impossible_budget 344 impossible_budget_344
  · exact root_excluded_of_impossible_budget 346 impossible_budget_346
  · exact root_excluded_of_impossible_budget 347 impossible_budget_347
  · exact root_excluded_of_impossible_budget 348 impossible_budget_348
  · exact root_excluded_of_impossible_budget 349 impossible_budget_349
  · exact root_excluded_of_impossible_budget 351 impossible_budget_351
  · exact root_excluded_of_impossible_budget 352 impossible_budget_352
  · exact root_excluded_of_impossible_budget 353 impossible_budget_353
  · exact root_excluded_of_impossible_budget 356 impossible_budget_356

end FiveColour.Physical
