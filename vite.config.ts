import { defineConfig } from 'vite'
import react from '@vitejs/plugin-react-swc'
import { viteStaticCopy } from 'vite-plugin-static-copy'
import { normalizePath } from 'vite'
import path from 'node:path'
import svgr from "vite-plugin-svgr"
import { nodePolyfills } from 'vite-plugin-node-polyfills'
import importMetaUrlPlugin from '@codingame/esbuild-import-meta-url-plugin'


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
          src: [
            normalizePath(path.resolve(__dirname, './node_modules/lean4monaco/node_modules/@leanprover/infoview/dist/*')),
            normalizePath(path.resolve(__dirname, './node_modules/lean4monaco/dist/webview/webview.js')),
          ],
          dest: 'infoview'
        },
        {
          src: [
            normalizePath(path.resolve(__dirname, './node_modules/lean4monaco/node_modules/@leanprover/infoview/dist/codicon.ttf'))
          ],
          dest: 'assets'
        }
      ]
    }),
    nodePolyfills({
      overrides: {
        fs: 'memfs',
      },
    }),
  ],
  publicDir: "client/public",
  base: "/", // setting this to `/leangame/` means the server is now accessible at `localhost:3000/leangame`
  optimizeDeps: {
    exclude: ['games'],
    esbuildOptions: {
      plugins: [importMetaUrlPlugin]
    }
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
