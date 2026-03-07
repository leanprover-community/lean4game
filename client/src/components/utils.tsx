import * as React from 'react'
import { Box, CircularProgress } from "@mui/material"
import 'katex/dist/katex.min.css' // `rehype-katex` does not import the CSS for you

/** Simple loading icon */
export function LoadingIcon () {
  return <Box display="flex" alignItems="center" justifyContent="center" sx={{ flex: 1, height: "calc(100vh - 64px)" }}>
    <CircularProgress />
  </Box>
}
