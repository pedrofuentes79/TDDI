-- Bootstrap lazy.nvim
local lazypath = vim.fn.stdpath("data") .. "/lazy/lazy.nvim"
if not vim.loop.fs_stat(lazypath) then
  vim.fn.system({
    "git",
    "clone",
    "--filter=blob:none",
    "https://github.com/folke/lazy.nvim.git",
    "--branch=stable", -- latest stable release
    lazypath,
  })
end
vim.opt.rtp:prepend(lazypath)

-- Set the leader key
vim.g.mapleader = '\'

-- Cornelis configuration (must be set before plugins load)
vim.g.cornelis_use_global_binary = 1

-- Basic Neovim options for Agda development
vim.opt.number = true
vim.opt.relativenumber = true
vim.opt.expandtab = true
vim.opt.shiftwidth = 2
vim.opt.tabstop = 2
vim.opt.smartindent = true
vim.opt.termguicolors = true

-- Plugin setup
require("lazy").setup({
  -- Load nvim-hs.vim first as it's required by cornelis
  {
    "neovimhaskell/nvim-hs.vim",
    lazy = false, -- Load immediately
    priority = 1000, -- High priority to load first
  },
  {
    "isovector/cornelis",
    dependencies = {
      "kana/vim-textobj-user",
    },
    ft = "agda",
    config = function()
      require("cornelis").setup()
      -- Define user commands after cornelis is loaded
      vim.api.nvim_create_user_command('CL', 'CornelisLoad', { nargs = 0, desc = "Cornelis Load" })
      vim.api.nvim_create_user_command('CE', 'CornelisTypeContext', { nargs = 0, desc = "Cornelis Type Context" })
      vim.api.nvim_create_user_command('CC', 'CornelisMakeCase', { nargs = 0, desc = "Cornelis Make Case" })
    end,
  },
  -- Optional: Add some useful plugins for Agda development
  {
    "nvim-treesitter/nvim-treesitter",
    build = ":TSUpdate",
    config = function()
      require("nvim-treesitter.configs").setup({
        ensure_installed = { "agda" },
        highlight = { enable = true },
      })
    end,
  },
})

-- Explicitly source agda.vim ftplugin to ensure Cornelis commands are available
vim.cmd("source " .. vim.fn.stdpath("data") .. "/lazy/cornelis/ftplugin/agda.vim")

-- Key mappings for cornelis
-- vim.keymap.set('n', '<leader>l', ':CornelisLoad<CR>', { silent = true, desc = "Cornelis Load" })
-- vim.keymap.set('n', '<leader>r', ':CornelisRefine<CR>', { silent = true, desc = "Cornelis Refine" })
-- vim.keymap.set('n', '<leader>d', ':CornelisMakeCase<CR>', { silent = true, desc = "Cornelis Make Case" })
-- vim.keymap.set('n', '<leader>n', 'vim.cmd(":CornelisNormalize")', { silent = true, desc = "Cornelis Normalize" })
