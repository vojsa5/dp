package microc.util

import java.io.{File, InputStream}
import scala.util.Using

object IOUtil {
  implicit class FilesOps(that: File) {
    def readAll(): String = java.nio.file.Files.readString(that.toPath)
  }

  implicit class InputStreamOpts(that: InputStream) {
    def readAll(): String = Using(that)(stream => new String(stream.readAllBytes(), "UTF-8")).get
  }
}
