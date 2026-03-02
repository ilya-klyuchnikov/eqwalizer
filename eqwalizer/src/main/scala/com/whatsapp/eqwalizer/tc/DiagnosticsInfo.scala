/* Copyright (c) Meta Platforms, Inc. and affiliates. All rights reserved.
 *
 * This source code is licensed under the Apache 2.0 license found in
 * the LICENSE file in the root directory of this source tree.
 */

package com.whatsapp.eqwalizer.tc

import com.whatsapp.eqwalizer.util.Diagnostic.Diagnostic

import scala.collection.mutable

class DiagnosticsInfo {
  private val moduleDiagnosticsInfo: mutable.ListBuffer[Diagnostic] = mutable.ListBuffer.empty
  private var suppressCount: Int = 0

  def add(diag: Diagnostic): Unit = {
    if (suppressCount == 0)
      moduleDiagnosticsInfo.addOne(diag)
  }

  def withSuppressed[T](block: => T): T = {
    suppressCount += 1
    try block
    finally suppressCount -= 1
  }

  def popErrors(): List[Diagnostic] = {
    val errors = moduleDiagnosticsInfo.distinct.toList
    moduleDiagnosticsInfo.clear()
    errors
  }
}
