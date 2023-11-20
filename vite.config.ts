import { defineConfig } from 'vite'
import react from '@vitejs/plugin-react-swc'
import { viteStaticCopy } from 'vite-plugin-static-copy'
import svgr from "vite-plugin-svgr"

// https://vitejs.dev/config/
export default defineConfig({
  //root: 'client/src',
  build: {
    // Relative to the root
    // Note: This has to match the path in `server/index.mjs`
    outDir: 'client/dist',
  },
  plugins: [
    react(),
    svgr({
      svgrOptions: {
        // svgr options
      },
    }),
    viteStaticCopy({
      targets: [
        {
          src: 'node_modules/@leanprover/infoview/dist/*.production.min.js',
          dest: '.'
        }
      ]
    })
  ],
  publicDir: "client/public",
  server: {
    port: 3000,
    proxy: {
      '/websocket': {
        target: 'ws://localhost:8080',
        ws: true
      },
      '/import': {
        target: 'http://localhost:8080',
      },
    }
  },
  resolve: {
    alias: {
      path: "path-browserify",
    },
  },
})
