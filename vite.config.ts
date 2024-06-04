import { defineConfig } from 'vite'
import react from '@vitejs/plugin-react-swc'
import { viteStaticCopy } from 'vite-plugin-static-copy'
import svgr from "vite-plugin-svgr"

const backendPort = process.env.PORT || 8080;
const clientPort = process.env.CLIENT_PORT || 3000;

// https://vitejs.dev/config/
export default defineConfig({
  //root: 'client/src',
  build: {
    // Relative to the root
    // Note: This has to match the path in `relay/index.mjs`
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
  optimizeDeps: {
    exclude: ['games']
  },
  server: {
    port: Number(clientPort),
    proxy: {
      '/websocket': {
        target: `ws://localhost:${backendPort}`,
        ws: true
      },
      '/import': {
        target: `http://localhost:${backendPort}`,
      },
      '/data': {
        target: `http://localhost:${backendPort}`,
      },
      '/i18n': {
        target: `http://localhost:${backendPort}`,
      },
    }
  },
  resolve: {
    alias: {
      path: "path-browserify",
    },
  },
})
